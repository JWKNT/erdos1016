import Mathlib

set_option autoImplicit false

/-!
# The second-moment summation step for the graphical cylinder bound

This file isolates the finite summation argument in the paper's Graphical
cylinder bound.  A family of affine cylinders supplies numbers `p i` (their
uniform probabilities) and `q i j` (their pairwise intersection probabilities).
The linear-algebraic cylinder calculation gives the pair bounds below, while
the triple-intersection argument bounds the exceptional partners.  This lemma
then performs the second-moment sum without losing the common one-dimensional
mode.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite second-moment summation from the pairwise cylinder bounds.

`p i` is the probability of cylinder `i`, `q i j` the joint probability,
and `exceptional i j` indicates that the common information has dimension at
least two.  For each `i`, there are at most `K` exceptional partners.
-/
theorem second_moment_of_cylinder_bounds
    (p : ι → ℝ) (q : ι → ι → ℝ) (exceptional : ι → ι → Prop)
    [DecidableRel exceptional]
    (K : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hdiag : ∀ i, q i i ≤ p i)
    (hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      q i j ≤ 2 * p i * p j)
    (hexceptional : ∀ i j, exceptional i j → q i j ≤ p i)
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ K) :
    (∑ i, ∑ j, q i j) ≤
      2 * (∑ i, p i) ^ 2 + (1 + K) * (∑ i, p i) := by
  classical
  let P := ∑ i, p i
  have hsum :
      (∑ i, ∑ j, q i j) ≤
        ∑ i, ∑ j, (2 * p i * p j +
          (if exceptional i j then p i else 0) +
          (if i = j then p i else 0)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases he : exceptional i j
    · have hq := hexceptional i j he
      have hpi := hp i
      have hpij : 0 ≤ p i * p j := mul_nonneg hpi (hp j)
      by_cases hij : i = j
      · subst j
        have hbase : 0 ≤ 2 * p i * p i := by positivity
        simp [he]
        nlinarith [hpi, hbase, hq]
      · have hbase : 0 ≤ 2 * p i * p j + p i := by
          nlinarith [hpi, hpij]
        simp [he, hij]
        nlinarith [hpi, hpij, hq]
    · by_cases hij : i = j
      · subst j
        have hq := hdiag i
        have hpi := hp i
        have hbase : 0 ≤ 2 * p i * p i := by nlinarith [sq_nonneg (p i)]
        simp [he]
        nlinarith [hbase, hq]
      · have hq := hordinary i j hij he
        simpa [he, hij] using hq
  have hpair :
      (∑ i, ∑ j, (2 * p i * p j : ℝ)) = 2 * P ^ 2 := by
    simp [P, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm,
      mul_comm, sq]
  have hexsum :
      (∑ i, ∑ j, (if exceptional i j then p i else 0 : ℝ)) ≤ K * P := by
    calc
      (∑ i, ∑ j, (if exceptional i j then p i else 0 : ℝ))
          = ∑ i, p i * ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_filter]
              simp [mul_comm]
      _ ≤ ∑ i, p i * K := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hpartners i) (hp i)
      _ = K * P := by simp [P, Finset.mul_sum, mul_comm]
  have hdiasum :
      (∑ i, ∑ j, (if i = j then p i else 0 : ℝ)) = P := by
    simp [P]
  calc
    (∑ i, ∑ j, q i j)
        ≤ ∑ i, ∑ j, (2 * p i * p j +
            (if exceptional i j then p i else 0) +
            (if i = j then p i else 0)) := hsum
    _ = (∑ i, ∑ j, (2 * p i * p j : ℝ)) +
          (∑ i, ∑ j, (if exceptional i j then p i else 0 : ℝ)) +
          (∑ i, ∑ j, (if i = j then p i else 0 : ℝ)) := by
            simp only [Finset.sum_add_distrib]
    _ ≤ 2 * P ^ 2 + K * P + P := by
          rw [hpair, hdiasum]
          nlinarith [hexsum]
    _ = 2 * (∑ i, p i) ^ 2 + (1 + K) * (∑ i, p i) := by
          dsimp [P]
          ring

end Erdos1016.Proof.GraphicalMoments
