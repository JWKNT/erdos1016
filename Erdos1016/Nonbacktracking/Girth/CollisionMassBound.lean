import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Summing the high-girth collision slices

This is the finite summation step in the paper's estimate
`S_L - W_L ≤ (9/4) L² 2^{-s} S_L`. The graph-specific suffix and core
decomposition produce the per-length slice bound `slice_bound`; the lemma
here sums those bounds and the paper's `Σ V_a ≤ 3 L S_L` tail estimate.
-/

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.HighGirthCollisionArithmetic

/-- Normalized ordinary closed-walk mass at lengths below `ℓ`. -/
def prefixMass (V : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (ℓ - 1), V a

/-- The total collision mass, divided by the trace normalization `2ℓ`. -/
def normalizedCollisionMass (bad : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 L, bad ℓ / (2 * (ℓ : ℝ))

/-- The slice estimate from the suffix argument, together with the total
ordinary closed-walk bound, implies the aggregate collision error bound in
equation (4.9). The `slice_bound` is the graph-specific hypothesis; it is
obtained by charging a nonsimple cyclic walk to a split position and then
using the unique-suffix estimate. -/
theorem collision_error_sum_le
    (V bad : ℕ → ℝ) (L s : ℕ) (S : ℝ)
    (hS : 0 ≤ S)
    (hVnonneg : ∀ a ∈ Finset.Icc 1 L, 0 ≤ V a)
    (hVsum : (∑ a ∈ Finset.Icc 1 L, V a) ≤ (3 : ℝ) * L * S)
    (slice_bound : ∀ ℓ ∈ Finset.Icc 1 L,
      bad ℓ ≤ (3 / 2 : ℝ) * (ℓ : ℝ) * (1 / 2 : ℝ) ^ s * prefixMass V ℓ) :
    normalizedCollisionMass bad L ≤
      (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s * S := by
  classical
  let q : ℝ := (1 / 2 : ℝ) ^ s
  let Vtot : ℝ := ∑ a ∈ Finset.Icc 1 L, V a
  have hq : 0 ≤ q := by positivity
  have hVtot : 0 ≤ Vtot := by
    dsimp [Vtot]
    apply Finset.sum_nonneg
    intro a ha
    exact hVnonneg a ha
  have hprefix_le (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 L) :
      prefixMass V ℓ ≤ Vtot := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      have ha' := Finset.mem_Icc.mp ha
      have hℓ' := Finset.mem_Icc.mp hℓ
      simp only [Finset.mem_Icc]
      exact ⟨ha'.1, ha'.2.trans (Nat.sub_le ℓ 1 |>.trans hℓ'.2)⟩
    · intro a ha hnot
      exact hVnonneg a ha
  have hcardIcc : (Finset.Icc 1 L).card = L := by
    simp
  have hprefix_sum :
      (∑ ℓ ∈ Finset.Icc 1 L, prefixMass V ℓ) ≤ (L : ℝ) * Vtot := by
    calc
      _ ≤ ∑ _ℓ ∈ Finset.Icc 1 L, Vtot := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        exact hprefix_le ℓ hℓ
      _ = (L : ℝ) * Vtot := by rw [← hcardIcc]; simp
  have hslice_sum :
      normalizedCollisionMass bad L ≤
        ((3 / 4 : ℝ) * q) *
          (∑ ℓ ∈ Finset.Icc 1 L, prefixMass V ℓ) := by
    unfold normalizedCollisionMass
    calc
      (∑ ℓ ∈ Finset.Icc 1 L, bad ℓ / (2 * (ℓ : ℝ))) ≤
          ∑ ℓ ∈ Finset.Icc 1 L, (3 / 4 : ℝ) * q * prefixMass V ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hℓpos : 0 < (ℓ : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hℓ).1
        have hden : 0 < 2 * (ℓ : ℝ) := by positivity
        have hb := slice_bound ℓ hℓ
        have hb' : bad ℓ ≤
            (3 / 2 : ℝ) * (ℓ : ℝ) * q * prefixMass V ℓ := by
          simpa [q] using hb
        calc
          bad ℓ / (2 * (ℓ : ℝ)) ≤
              ((3 / 2 : ℝ) * (ℓ : ℝ) * q * prefixMass V ℓ) /
                (2 * (ℓ : ℝ)) := div_le_div_of_nonneg_right hb' hden.le
          _ = (3 / 4 : ℝ) * q * prefixMass V ℓ := by
                field_simp
                ring
      _ = ((3 / 4 : ℝ) * q) *
          (∑ ℓ ∈ Finset.Icc 1 L, prefixMass V ℓ) := by
            rw [← Finset.mul_sum]
  have hfactor : 0 ≤ (3 / 4 : ℝ) * q * (L : ℝ) := by positivity
  have hVsum' : Vtot ≤ (3 : ℝ) * (L : ℝ) * S := by
    simpa [Vtot] using hVsum
  calc
    normalizedCollisionMass bad L ≤
        ((3 / 4 : ℝ) * q) *
          (∑ ℓ ∈ Finset.Icc 1 L, prefixMass V ℓ) := hslice_sum
    _ ≤ ((3 / 4 : ℝ) * q) * ((L : ℝ) * Vtot) := by
      exact mul_le_mul_of_nonneg_left hprefix_sum (by positivity)
    _ ≤ ((3 / 4 : ℝ) * q) *
          ((L : ℝ) * ((3 : ℝ) * (L : ℝ) * S)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hVsum' (by positivity)
      · positivity
    _ = (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s * S := by
      dsimp [q]
      ring

end Erdos1016.Proof.HighGirthCollisionArithmetic
end
