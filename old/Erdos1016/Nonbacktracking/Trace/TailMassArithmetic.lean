import Mathlib

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.CycleRunTailArithmetic

open scoped BigOperators

/-- Normalized cyclic-core mass through length `L`. -/
def corePrefixMass (T : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 L, T t

/-- Core mass available after deleting a tail of length `j`; the original
length is `t + 2j`, so only core lengths through `L - 2j` can contribute. -/
def shiftedCoreMass (T : ℕ → ℝ) (L j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (L - 2 * j), T t

theorem shiftedCoreMass_le (T : ℕ → ℝ) (L j : ℕ)
    (hT : ∀ t ∈ Finset.Icc 1 L, 0 ≤ T t) :
    shiftedCoreMass T L j ≤ corePrefixMass T L := by
  unfold shiftedCoreMass corePrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    simp only [Finset.mem_Icc]
    exact ⟨ht'.1, ht'.2.trans (Nat.sub_le L (2 * j))⟩
  · intro t ht hnot
    exact hT t ht

/-- The tail-attachment weights sum to at most one half. -/
theorem tail_kernel_sum_le_half (L : ℕ) :
    (∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1)) ≤ 1 / 2 := by
  have hsum :
      (∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1)) =
        (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ (L + 1) := by
    induction L with
    | zero => simp
    | succ L ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1)]
        rw [ih]
        rw [show L + 1 + 1 = (L + 1) + 1 by omega, pow_succ]
        ring
  rw [hsum]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ (L + 1) := by positivity
  linarith

/-- Geometric tail summation: if the mass exposed after removing a tail of
each length is bounded by the total cyclic-core mass, then all tail
attachments together add at most half that mass. This is the finite
arithmetic step behind the paper's `sum V_ell <= 3 L S_L`; graph-specific
tail stripping and reindexing are explicit premises below. -/
theorem weighted_tail_mass_le_half
    (L : ℕ) (coreMass : ℝ) (shiftedMass : ℕ → ℝ)
    (hcore : 0 ≤ coreMass)
    (hshift : ∀ j ∈ Finset.Icc 1 L, shiftedMass j ≤ coreMass) :
    (∑ j ∈ Finset.Icc 1 L,
      (1 / 2 : ℝ) ^ (j + 1) * shiftedMass j) ≤ coreMass / 2 := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 L) :
      (1 / 2 : ℝ) ^ (j + 1) * shiftedMass j ≤
        (1 / 2 : ℝ) ^ (j + 1) * coreMass := by
    apply mul_le_mul_of_nonneg_left (hshift j hj)
    positivity
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 L,
        (1 / 2 : ℝ) ^ (j + 1) * coreMass := by
          apply Finset.sum_le_sum
          intro j hj
          exact hterm j hj
    _ = (∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1)) * coreMass := by
          rw [Finset.sum_mul]
    _ ≤ (1 / 2 : ℝ) * coreMass := by
          exact mul_le_mul_of_nonneg_right (tail_kernel_sum_le_half L) hcore
    _ = coreMass / 2 := by ring

/-- Aggregate finite trace-to-core conversion. `hdecomp` is the graph-side
tail-stripping and reindexing statement: ordinary closed-walk mass is at most
cyclic trace mass plus the tail contributions indexed by `shiftedMass`.
`htrace` is the normalization `sum T_ell <= 2 L S_L`. -/
theorem ordinary_closed_mass_le_three_L_trace
    (L : ℕ) (closedMass coreMass traceMass : ℝ)
    (T : ℕ → ℝ)
    (hcore : 0 ≤ coreMass)
    (hdecomp : closedMass ≤ coreMass +
      ∑ j ∈ Finset.Icc 1 L,
        (1 / 2 : ℝ) ^ (j + 1) * shiftedCoreMass T L j)
    (hT : ∀ t ∈ Finset.Icc 1 L, 0 ≤ T t)
    (hcore_eq : coreMass = corePrefixMass T L)
    (htrace : coreMass ≤ 2 * (L : ℝ) * traceMass)
    :
    closedMass ≤ 3 * (L : ℝ) * traceMass := by
  have hshift (j : ℕ) (hj : j ∈ Finset.Icc 1 L) :
      shiftedCoreMass T L j ≤ coreMass := by
    rw [hcore_eq]
    exact shiftedCoreMass_le T L j hT
  have htail := weighted_tail_mass_le_half L coreMass
    (shiftedCoreMass T L) hcore hshift
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  calc
    closedMass ≤ coreMass +
        ∑ j ∈ Finset.Icc 1 L,
          (1 / 2 : ℝ) ^ (j + 1) * shiftedCoreMass T L j := hdecomp
    _ ≤ coreMass + coreMass / 2 := add_le_add_left htail _
    _ ≤ 3 * (L : ℝ) * traceMass := by nlinarith [htrace, hcore, hL]

end Erdos1016.Proof.CycleRunTailArithmetic
end
