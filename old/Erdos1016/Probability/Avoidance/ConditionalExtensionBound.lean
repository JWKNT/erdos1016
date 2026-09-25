import Erdos1016.Probability.Moments.OrderedFactorialMoments
import Erdos1016.Probability.Moments.ConditionalRecurrence
import Erdos1016.Probability.Moments.LowOrderMoments

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

local instance extensionAvoidanceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Probability that all entries of an ordered tuple occur. -/
def tupleEventProbability {Ω α : Type*} [Fintype Ω] {n : ℕ}
    (P : α → Ω → Prop) (u : Fin n → α) : ℝ :=
  Finite.density (fun ω => ∀ i, P (u i) ω)

theorem tupleEventProbability_nonneg {Ω α : Type*} [Fintype Ω] {n : ℕ}
    (P : α → Ω → Prop) (u : Fin n → α) :
    0 ≤ tupleEventProbability P u := Finite.density_nonneg _

/-- Extending a tuple only shrinks its event. -/
theorem tupleEventProbability_snoc_le {Ω α : Type*} [Fintype Ω] {n : ℕ}
    (P : α → Ω → Prop) (u : Fin n → α) (a : α) :
    tupleEventProbability P (Fin.snoc u a) ≤ tupleEventProbability P u := by
  unfold tupleEventProbability Finite.density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finite.count_mono
  intro ω h i
  simpa using h i.castSucc

/-- The usual conditional multiplication identity, including zero-probability
conditioning events. Nesting forces the numerator to vanish in that case. -/
theorem tupleEventProbability_snoc_mul_div {Ω α : Type*} [Fintype Ω] {n : ℕ}
    (P : α → Ω → Prop) (u : Fin n → α) (a : α) :
    tupleEventProbability P (Fin.snoc u a) = tupleEventProbability P u *
      (tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u) := by
  by_cases hz : tupleEventProbability P u = 0
  · have hn := tupleEventProbability_nonneg P (Fin.snoc u a)
    have hu := tupleEventProbability_snoc_le P u a
    rw [hz] at hu ⊢
    simp only [zero_mul]
    linarith
  · field_simp

private theorem shifted_error_sum_eq (K : ℕ) (hK : 2 ≤ K) (err : ℕ → ℝ) :
    (∑ j ∈ Finset.range (K + 1), if 2 ≤ j then err j / (j.factorial : ℝ) else 0) =
      ∑ k ∈ Finset.range (K - 1), err (k + 2) / ((k + 2).factorial : ℝ) := by
  have heq : K + 1 = 2 + (K - 1) := by omega
  rw [heq, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]
  congr 1
  funext k
  simp [add_comm]

/-- A family of local conditional laws gives the finite Poisson avoidance
bound. The hypotheses involve single-cycle extensions, a product lower law,
and pairwise incompatibility; no higher moment or avoidance estimate is an
input. -/
theorem finite_avoidance_le_of_conditional_extension_load
    {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (P : α → Ω → Prop) (K : ℕ) (hK : Even K) (hKtwo : 2 ≤ K)
    (R : α → α → Prop) (compatible : (k : ℕ) → (Fin k → α) → Prop)
    (w : α → ℝ) (lambdaVar d : ℝ)
    (hlambda : 0 < lambdaVar) (hd : 0 ≤ d)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = lambdaVar)
    (hmarginal : ∀ a, Finite.density (P a) = w a)
    (hcompatible : ∀ k ≤ K, ∀ u, Function.Injective u →
      ∀ ω, (∀ i, P (u i) ω) → compatible k u)
    (hprefix : ∀ k < K, ∀ u a, compatible (k + 1) (Fin.snoc u a) → compatible k u)
    (hfar : ∀ k < K, ∀ u a,
      Function.Injective (Fin.snoc u a) → compatible (k + 1) (Fin.snoc u a) →
      (∀ i, ¬ R (u i) a) →
      tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u = w a)
    (hnear : ∀ k < K, ∀ u, Function.Injective u → compatible k u → ∀ i : Fin k,
      (∑ a, if (Function.Injective (Fin.snoc u a) ∧
          compatible (k + 1) (Fin.snoc u a)) ∧ R (u i) a then
        tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u else 0) ≤ d)
    (hproduct : ∀ k ≤ K, ∀ u, Function.Injective u → compatible k u →
      tupleProduct w u ≤ tupleEventProbability P u)
    (hdiag : ∀ a, R a a)
    (hrow : ∀ a, (∑ b, if R a b then w b else 0) ≤ d)
    (hgood : ∀ k ≤ K, ∀ u,
      InvalidTupleMass.pairwiseRGood R k u → compatible k u) :
    Finite.density (fun ω => finiteEventCount Finset.univ P ω = 0) ≤
      Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) / ((K + 1).factorial : ℝ) +
        d * lambdaVar * Real.exp (lambdaVar + (Nat.choose K 2 : ℝ) * d / lambdaVar) := by
  classical
  let joint := fun (k : ℕ) (u : Fin k → α) => tupleEventProbability P u
  let err := fun j => 2 * (Nat.choose j 2 : ℝ) * d * lambdaVar ^ (j - 1) *
    Real.exp ((Nat.choose j 2 : ℝ) * d / lambdaVar)
  have hnormal (j : ℕ) (hj : j ≤ K) :
      (j.factorial : ℝ) * finiteFactorialMoment Finset.univ P j =
        orderedFactorialMoment j (compatible j) (joint j) :=
    factorial_mul_finiteFactorialMoment_eq_compatible_ordered P j (compatible j)
      (hcompatible j hj)
  have hzero : orderedFactorialMoment 0 (compatible 0) (joint 0) ≤ 1 := by
    rw [← hnormal 0 (by omega), finiteFactorialMoment_zero_eq_one]
    norm_num
  have hfar' (k : ℕ) (hk : k < K) (u : Fin k → α) (a : α)
      (hi : Function.Injective (Fin.snoc u a)) (hc : compatible (k + 1) (Fin.snoc u a))
      (hf : ∀ i, ¬ R (u i) a) : joint (k + 1) (Fin.snoc u a) = joint k u * w a := by
    dsimp [joint]
    rw [tupleEventProbability_snoc_mul_div P u a, hfar k hk u a hi hc hf]
  have hnear' (k : ℕ) (hk : k < K) (u : Fin k → α)
      (hi : Function.Injective u) (hc : compatible k u) (i : Fin k) :
      (∑ a, if (Function.Injective (Fin.snoc u a) ∧
          compatible (k + 1) (Fin.snoc u a)) ∧ R (u i) a then
        joint (k + 1) (Fin.snoc u a) else 0) ≤ joint k u * d := by
    have heq : (∑ a, if (Function.Injective (Fin.snoc u a) ∧
          compatible (k + 1) (Fin.snoc u a)) ∧ R (u i) a then
        joint (k + 1) (Fin.snoc u a) else 0) =
        joint k u * (∑ a, if (Function.Injective (Fin.snoc u a) ∧
          compatible (k + 1) (Fin.snoc u a)) ∧ R (u i) a then
        tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs
      · exact tupleEventProbability_snoc_mul_div P u a
      · exact (mul_zero _).symm
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hnear k hk u hi hc i)
      (tupleEventProbability_nonneg P u)
  have hraw (j : ℕ) (hj : j ∈ Finset.Icc 2 K) :
      |finiteFactorialMoment Finset.univ P j - lambdaVar ^ j / (j.factorial : ℝ)| ≤
        err j / (j.factorial : ℝ) := by
    have hjle := (Finset.mem_Icc.mp hj).2
    have hh := ordered_factorial_moment_error_of_extension_load j (by
        have := (Finset.mem_Icc.mp hj).1; omega) R compatible joint w lambdaVar d
      hlambda hd hw hsum hzero
      (fun k hk => hprefix k (hk.trans_le hjle))
      (fun k hk u _ _ => tupleEventProbability_nonneg P u)
      (fun k hk => hfar' k (hk.trans_le hjle))
      (fun k hk => hnear' k (hk.trans_le hjle))
      (hproduct j hjle) hdiag hrow (hgood j hjle)
    have herr : |orderedFactorialMoment j (compatible j) (joint j) - lambdaVar ^ j| ≤ err j := by
      dsimp [err]
      have hnonneg : 0 ≤ (Nat.choose j 2 : ℝ) * d * lambdaVar ^ (j - 1) *
          Real.exp ((Nat.choose j 2 : ℝ) * d / lambdaVar) := by positivity
      linarith
    have heq : finiteFactorialMoment Finset.univ P j - lambdaVar ^ j / (j.factorial : ℝ) =
        (orderedFactorialMoment j (compatible j) (joint j) - lambdaVar ^ j) /
          (j.factorial : ℝ) := by
      rw [← hnormal j hjle]
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (j.factorial : ℝ))]
    exact div_le_div_of_nonneg_right herr (by positivity)
  have hbudget := sum_source_factorial_moment_errors_le K hKtwo lambdaVar d hlambda hd err
    (fun _ _ => le_rfl)
  rw [← shifted_error_sum_eq K hKtwo err] at hbudget
  have hmass : BoundaryDecay.eventMass Finset.univ P = lambdaVar := by
    simp [BoundaryDecay.eventMass, hmarginal, hsum]
  apply FactorialMomentAvoidance.finite_avoidance_le_poisson_of_factorial_moment_errors
    Finset.univ P K hK lambdaVar _ hlambda.le err
  · simpa [hmass] using finiteFactorialMoment_low_orders (Finset.univ : Finset α) P
  · exact hraw
  · exact hbudget

end Erdos1016.Proof.ConditionalMoments
