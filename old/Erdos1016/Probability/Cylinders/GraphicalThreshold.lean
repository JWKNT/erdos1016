import Erdos1016.Probability.Moments.CylinderSecondMoment
import Erdos1016.Probability.Moments.PaleyZygmund

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalThreshold

open Erdos1016.Proof.FinitePaleyZygmund
open Erdos1016.Proof.GraphicalMoments

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- Number of events in a finite family which hold at a sample point. -/
noncomputable def eventCount (E : ι → Ω → Prop) (x : Ω) : ℝ := by
  classical
  exact ∑ i, if E i x then 1 else 0

/-- Probability of an event under the uniform distribution on `Ω`. -/
noncomputable def eventProbability (P : Ω → Prop) : ℝ := probability P

/-- A family of cylinder events, their first and pair probabilities, and the
exceptional-partner hypotheses from the graphical second-moment estimate imply
the Section 3 threshold bound for the number of cylinders containing a random
sample point. -/
theorem graphical_cylinder_threshold
    (E : ι → Ω → Prop) (exceptional : ι → ι → Prop) [DecidableRel exceptional]
    (K a μ : ℝ)
    (ha : 0 ≤ a) (hμ : a < μ) (hK : 0 ≤ K)
    (hmean : μ = ∑ i, eventProbability (E i))
    (hdiag : ∀ i, eventProbability (fun x => E i x ∧ E i x) ≤ eventProbability (E i))
    (hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤
        2 * eventProbability (E i) * eventProbability (E j))
    (hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤ eventProbability (E i))
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ K) :
    (μ - a) ^ 2 / (2 * μ ^ 2 + (1 + K) * μ) ≤
      probability (fun x => a ≤ eventCount E x) := by
  classical
  let p : ι → ℝ := fun i => eventProbability (E i)
  let q : ι → ι → ℝ := fun i j => eventProbability (fun x => E i x ∧ E j x)
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    dsimp [p, eventProbability, probability]
    positivity
  have hsec := second_moment_of_cylinder_bounds p q exceptional K hp
    (by simpa [p, q] using hdiag)
    (by simpa [p, q] using hordinary)
    (by simpa [p, q] using hexceptional)
    hpartners
  have hcountMean : mean (eventCount E) = μ := by
    have hmeanIdentity : mean (eventCount E) = ∑ i, eventProbability (E i) := by
      unfold mean eventCount eventProbability probability
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_boole]
      simp [Finset.sum_div]
    rw [hmean]
    exact hmeanIdentity
  have hcountSecond :
      mean (fun x => eventCount E x ^ 2) ≤ 2 * μ ^ 2 + (1 + K) * μ := by
    have hidentity :
        (∑ x, (∑ i, if E i x then (1 : ℝ) else 0) ^ 2) =
          ∑ i, ∑ j, (∑ x, if E i x ∧ E j x then (1 : ℝ) else 0) := by
      calc
        (∑ x, (∑ i, if E i x then (1 : ℝ) else 0) ^ 2)
            = ∑ x, ∑ i, ∑ j,
                (if E i x then (1 : ℝ) else 0) * (if E j x then 1 else 0) := by
                  simp_rw [sq, Finset.sum_mul_sum]
        _ = ∑ i, ∑ j, ∑ x,
                (if E i x then (1 : ℝ) else 0) * (if E j x then 1 else 0) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, ∑ x, if E i x ∧ E j x then (1 : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro j _
                  apply Finset.sum_congr rfl
                  intro x _
                  by_cases hi : E i x <;> by_cases hj : E j x <;> simp [hi, hj]
    have hprobIdentity : ∀ i j,
        (∑ x, if E i x ∧ E j x then (1 : ℝ) else 0) =
          eventProbability (fun x => E i x ∧ E j x) * (Fintype.card Ω : ℝ) := by
      intro i j
      unfold eventProbability probability
      rw [Finset.sum_boole]
      have hN : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
      field_simp
      congr 1
      ext x
      simp
    have hMomentEq :
        mean (fun x => eventCount E x ^ 2) = ∑ i, ∑ j, q i j := by
      change (∑ x, (∑ i, if E i x then (1 : ℝ) else 0) ^ 2) /
          (Fintype.card Ω : ℝ) = ∑ i, ∑ j, q i j
      rw [hidentity]
      simp_rw [hprobIdentity]
      simp_rw [← Finset.sum_mul]
      dsimp [q]
      field_simp
    rw [hMomentEq]
    dsimp [p] at hsec
    rw [← hmean] at hsec
    exact hsec
  exact cylinder_count_threshold (eventCount E) a μ K
    (fun x => by
      unfold eventCount
      exact Finset.sum_nonneg fun i hi => by split_ifs <;> norm_num)
    ha hcountMean hcountSecond hμ hK

end Erdos1016.Proof.GraphicalThreshold
