import Mathlib

set_option autoImplicit false

/-!
# Finite Paley–Zygmund threshold estimate

For a nonnegative function on a finite uniform space, a first moment above a
threshold and a second-moment bound force a lower bound on the probability of
reaching that threshold.  The proof uses only finite sums and Cauchy–Schwarz.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.FinitePaleyZygmund

variable {Ω : Type*} [Fintype Ω]

/-- Uniform mean of a real-valued function on a finite sample space. -/
def mean (f : Ω → ℝ) : ℝ := (∑ x, f x) / (Fintype.card Ω : ℝ)

/-- Uniform probability of an event on a finite sample space. -/
noncomputable def probability (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- Finite Paley–Zygmund inequality with an arbitrary threshold. -/
theorem threshold_probability_lower_bound
    [Nonempty Ω] (Z : Ω → ℝ) (a μ B : ℝ)
    (hZ : ∀ x, 0 ≤ Z x)
    (ha : 0 ≤ a)
    (hmean : mean Z = μ)
    (hsecond : mean (fun x => Z x ^ 2) ≤ B)
    (hμ : a < μ)
    (hB : 0 < B) :
    (μ - a) ^ 2 / B ≤ probability (fun x => a ≤ Z x) := by
  classical
  let N : ℝ := Fintype.card Ω
  let high : Finset Ω := Finset.univ.filter (fun x => a ≤ Z x)
  let low : Finset Ω := Finset.univ.filter (fun x => ¬ a ≤ Z x)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Ω›
  have htotal : (∑ x, Z x) = μ * N := by
    have hm := hmean
    dsimp [mean, N] at hm
    exact (div_eq_iff (by positivity : (Fintype.card Ω : ℝ) ≠ 0)).1 hm
  have htotal2 : (∑ x, Z x ^ 2) ≤ B * N := by
    have hs := hsecond
    dsimp [mean, N] at hs
    exact (div_le_iff₀ hN).1 hs
  have hlow :
      (∑ x ∈ low, Z x) ≤ a * N := by
    calc
      (∑ x ∈ low, Z x) ≤ ∑ x ∈ low, a := by
        apply Finset.sum_le_sum
        intro x hx
        have hxnot : ¬ a ≤ Z x := (Finset.mem_filter.mp hx).2
        have hxlt : Z x < a := lt_of_not_ge hxnot
        exact hxlt.le
      _ = (low.card : ℝ) * a := by simp [mul_comm]
      _ ≤ (Finset.univ.card : ℝ) * a := by
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (Finset.card_le_card (show low ⊆ Finset.univ from Finset.filter_subset _ _))) ha
      _ = a * N := by simp [N, mul_comm]
  have hsplit : (∑ x ∈ high, Z x) + (∑ x ∈ low, Z x) = ∑ x, Z x := by
    simpa [high, low] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => a ≤ Z x) Z)
  have hhighLower : (μ - a) * N ≤ ∑ x ∈ high, Z x := by
    nlinarith [htotal, hsplit, hlow]
  have hhighNonneg : 0 ≤ ∑ x ∈ high, Z x :=
    Finset.sum_nonneg (fun x hx => hZ x)
  have hhighSq :
      (∑ x ∈ high, Z x) ^ 2 ≤
        (∑ x ∈ high, Z x ^ 2) * (high.card : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq high Z (fun _ => (1 : ℝ))
    simpa using hcs
  have hsqSubset :
      (∑ x ∈ high, Z x ^ 2) ≤ ∑ x, Z x ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (show high ⊆ Finset.univ from Finset.filter_subset _ _)
      (fun x _ _ => sq_nonneg (Z x))
  have hhighCard : 0 ≤ (high.card : ℝ) := Nat.cast_nonneg _
  have hmomentProduct :
      (μ - a) ^ 2 * N ≤ B * (high.card : ℝ) := by
    have hμa : 0 < μ - a := sub_pos.mpr hμ
    have hsqLower : 0 ≤ (μ - a) * N := by positivity
    have hlowSq :
        ((μ - a) * N) ^ 2 ≤ (∑ x ∈ high, Z x) ^ 2 :=
      (sq_le_sq₀ hsqLower hhighNonneg).2 hhighLower
    have hsecondHigh :=
      mul_le_mul_of_nonneg_right (hsqSubset.trans htotal2) hhighCard
    have htwice :
        ((μ - a) ^ 2 * N) * N ≤ (B * (high.card : ℝ)) * N := by
      nlinarith [hlowSq, hhighSq, hsecondHigh]
    exact le_of_mul_le_mul_right htwice hN
  have hprob : probability (fun x => a ≤ Z x) = (high.card : ℝ) / N := by
    simp [probability, high, N]
  rw [hprob]
  exact (div_le_div_iff₀ hB hN).2 (by nlinarith [hmomentProduct])

/-- The version used in the paper, with the graphical-cylinder second-moment
bound substituted for `B`. -/
theorem cylinder_count_threshold
    [Nonempty Ω] (Z : Ω → ℝ) (a μ K : ℝ)
    (hZ : ∀ x, 0 ≤ Z x)
    (ha : 0 ≤ a)
    (hmean : mean Z = μ)
    (hsecond : mean (fun x => Z x ^ 2) ≤ 2 * μ ^ 2 + (1 + K) * μ)
    (hμ : a < μ)
    (hK : 0 ≤ K) :
    (μ - a) ^ 2 / (2 * μ ^ 2 + (1 + K) * μ) ≤
      probability (fun x => a ≤ Z x) := by
  have hμpos : 0 < μ := lt_of_le_of_lt ha hμ
  have hB : 0 < 2 * μ ^ 2 + (1 + K) * μ := by positivity
  exact threshold_probability_lower_bound Z a μ
    (2 * μ ^ 2 + (1 + K) * μ) hZ ha hmean hsecond hμ hB

end Erdos1016.Proof.FinitePaleyZygmund
