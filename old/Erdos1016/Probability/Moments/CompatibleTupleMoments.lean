import Erdos1016.Probability.Moments.Bonferroni
import Erdos1016.Probability.Moments.InvalidTupleMass

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

local instance forestBridgeDecidableRel {α : Type*} (R : α → α → Prop) :
    DecidableRel R := fun a b => Classical.propDecidable (R a b)



def tupleProduct {α : Type*} {j : ℕ} (w : α → ℝ) (u : Fin j → α) : ℝ :=
  ∏ k, w (u k)

noncomputable def orderedFactorialMoment {α : Type*} [Fintype α] (j : ℕ)
    (compatible : (Fin j → α) → Prop) (joint : (Fin j → α) → ℝ) : ℝ := by
  classical
  exact ∑ u : Fin j → α,
    if Function.Injective u ∧ compatible u then joint u else 0



noncomputable def invalidTupleProductMass {α : Type*} [Fintype α] (j : ℕ)
    (compatible : (Fin j → α) → Prop) (w : α → ℝ) : ℝ := by
  classical
  exact ∑ u : Fin j → α,
    if ¬ (Function.Injective u ∧ compatible u) then tupleProduct w u else 0

/-- The pairwise-R row-load recurrence bounds the invalid product mass whenever
every recursively R-good tuple is compatible. Diagonal R-pairs imply that
R-good tuples are injective. The compatibility premise is intentionally
abstract: discharging it for the physical cycle compatibility relation remains
open. -/
theorem invalid_tuple_product_mass_le_choose_two_of_pairwiseRGood
    {α : Type*} [Fintype α] (j : ℕ) (R : α → α → Prop)
    (compatible : (Fin j → α) → Prop) (w : α → ℝ) (lambdaVar d : ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hdiag : ∀ a, R a a)
    (hrow : ∀ a, (∑ b, if R a b then w b else 0) ≤ d)
    (hlambda : (∑ a, w a) = lambdaVar) (hd : 0 ≤ d)
    (hgood : ∀ u, InvalidTupleMass.pairwiseRGood R j u → compatible u) :
    invalidTupleProductMass j compatible w ≤
      (Nat.choose j 2 : ℝ) * d * lambdaVar ^ (j - 1) := by
  classical
  have hgeneric :=
    InvalidTupleMass.invalid_tuple_product_mass_le_choose_two
      j R w lambdaVar d hw hdiag hrow hlambda hd
  have hpoint (u : Fin j → α) :
      (if ¬ (Function.Injective u ∧ compatible u) then
        ∏ i, w (u i) else 0) ≤
      (if ¬ InvalidTupleMass.pairwiseRGood R j u then
        ∏ i, w (u i) else 0) := by
    by_cases hRgood : InvalidTupleMass.pairwiseRGood R j u
    · have hinj := InvalidTupleMass.pairwiseRGood_injective
        R hdiag j u hRgood
      have hcompatible := hgood u hRgood
      simp [hRgood, hinj, hcompatible]
    · have hweight : 0 ≤ ∏ i, w (u i) :=
        Finset.prod_nonneg fun i hi => hw (u i)
      by_cases hvalid : Function.Injective u ∧ compatible u
      · simp [hRgood, hvalid, hweight]
      · simp [hRgood, hvalid]
  have hmass : invalidTupleProductMass j compatible w ≤
      InvalidTupleMass.invalidTupleProductMass j R w := by
    unfold invalidTupleProductMass
    unfold InvalidTupleMass.invalidTupleProductMass
    apply Finset.sum_le_sum
    intro u hu
    exact hpoint u
  exact hmass.trans hgeneric







end Erdos1016.Proof.ConditionalMoments
