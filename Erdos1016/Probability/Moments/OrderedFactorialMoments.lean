import Erdos1016.Probability.Moments.CompatibleTupleMoments
import Mathlib.Data.Fintype.CardEmbedding

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

local instance finiteOrderedMomentDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private def injectionIntoSubtypeEquiv {α : Type*} (n : ℕ) (P : α → Prop) :
    {u : Fin n → α // Function.Injective u ∧ ∀ i, P (u i)} ≃
      (Fin n ↪ {a : α // P a}) where
  toFun u := ⟨fun i => ⟨u.1 i, u.2.2 i⟩,
    fun i j h => u.2.1 (congrArg Subtype.val h)⟩
  invFun u := ⟨fun i => (u i).1, fun i j h => u.injective (Subtype.ext h),
    fun i => (u i).2⟩
  left_inv u := by rfl
  right_inv u := by rfl

/-- Ordered injections into the active events count the descending factorial
of the number of active events. This identity also covers orders larger than
the family, and empty families. -/
theorem sum_injective_indicators_eq_factorial_choose
    {α : Type*} [Fintype α] (n : ℕ) (P : α → Prop) :
    (∑ u : Fin n → α, if Function.Injective u ∧ ∀ i, P (u i) then
      (1 : ℝ) else 0) =
        (n.factorial : ℝ) *
          (Nat.choose ((Finset.univ.filter P).card) n : ℝ) := by
  classical
  have hc := Fintype.card_congr (injectionIntoSubtypeEquiv n P)
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    Nat.descFactorial_eq_factorial_mul_choose] at hc
  have hactive : Fintype.card {a : α // P a} = (Finset.univ.filter P).card := by
    simp [Fintype.card_subtype]
  rw [hactive] at hc
  have htuples : (∑ u : Fin n → α, if Function.Injective u ∧ ∀ i, P (u i)
      then (1 : ℝ) else 0) =
      (Fintype.card {u : Fin n → α // Function.Injective u ∧ ∀ i, P (u i)} : ℝ) := by
    simp [Fintype.card_subtype]
  rw [htuples, hc, Nat.cast_mul]

/-- The unnormalized factorial moment is the sum of joint probabilities over
all ordered distinct choices. This is the exact bridge from tuple counting to
the finite Bonferroni moments. -/
theorem factorial_mul_finiteFactorialMoment_eq_ordered
    {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : α → Ω → Prop) (n : ℕ) :
    (n.factorial : ℝ) * finiteFactorialMoment Finset.univ P n =
      ∑ u : Fin n → α, if Function.Injective u then
        Finite.density (fun ω => ∀ i, P (u i) ω) else 0 := by
  classical
  have hpoint (ω : Ω) := sum_injective_indicators_eq_factorial_choose n (fun a => P a ω)
  have heq : (fun ω => (n.factorial : ℝ) *
      (Nat.choose (finiteEventCount Finset.univ P ω) n : ℝ)) =
      (fun ω => ∑ u : Fin n → α,
        BoundaryDecay.indicator (fun ω => Function.Injective u ∧ ∀ i, P (u i) ω) ω) := by
    funext ω
    change (n.factorial : ℝ) * (Nat.choose ((Finset.univ.filter (fun a => P a ω)).card) n : ℝ) = _
    rw [← hpoint ω]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : Function.Injective u ∧ ∀ i, P (u i) ω <;>
      simp [BoundaryDecay.indicator, hu]
  rw [finiteFactorialMoment, ← BoundaryDecay.average_mul_left, heq,
    BoundaryDecay.average_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [BoundaryDecay.average_indicator]
  by_cases hu : Function.Injective u
  · simp [hu]
  · simp [hu, Finite.density]

/-- An incompatible tuple can be deleted from the ordered sum when simultaneous
occurrence of its events would force compatibility. No independence is used. -/
theorem factorial_mul_finiteFactorialMoment_eq_compatible_ordered
    {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : α → Ω → Prop) (n : ℕ) (compatible : (Fin n → α) → Prop)
    (hcompatible : ∀ u, Function.Injective u →
      ∀ ω, (∀ i, P (u i) ω) → compatible u) :
    (n.factorial : ℝ) * finiteFactorialMoment Finset.univ P n =
      orderedFactorialMoment n compatible
        (fun u => Finite.density (fun ω => ∀ i, P (u i) ω)) := by
  classical
  rw [factorial_mul_finiteFactorialMoment_eq_ordered, orderedFactorialMoment]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : Function.Injective u
  · by_cases hc : compatible u
    · simp [hu, hc]
    · have hnone : ∀ ω, ¬ (∀ i, P (u i) ω) := fun ω hp => hc (hcompatible u hu ω hp)
      simp [hu, hc, Finite.density, Finite.count, hnone]
  · simp [hu]

end Erdos1016.Proof.ConditionalMoments
