import Erdos1016.Probability.Moments.FactorialMomentAvoidance

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

/-- The zeroth factorial moment of a nonempty finite uniform state space is
one. -/
theorem finiteFactorialMoment_zero_eq_one
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset ι) (P : ι → Ω → Prop) :
    finiteFactorialMoment s P 0 = 1 := by
  simp [finiteFactorialMoment, BoundaryDecay.average_const]

/-- The first normalized factorial moment is the expected event count, namely
the sum of the individual event densities. -/
theorem finiteFactorialMoment_one_eq_eventMass
    {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (P : ι → Ω → Prop) :
    finiteFactorialMoment s P 1 =
      ∑ i ∈ s, Finite.density (P i) := by
  classical
  have hpoint (ω : Ω) :
      (Nat.choose (finiteEventCount s P ω) 1 : ℝ) =
        BoundaryDecay.eventCount s P ω := by
    simp [finiteEventCount, BoundaryDecay.eventCount,
      BoundaryDecay.indicator]
  unfold finiteFactorialMoment
  simp_rw [hpoint]
  rw [BoundaryDecay.average_eventCount]
  rfl

/-- Exact agreement with the Poisson factorial moments at orders zero and one,
when the Poisson parameter is the total event mass. -/
theorem finiteFactorialMoment_low_orders
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset ι) (P : ι → Ω → Prop) :
    ∀ j, j < 2 → finiteFactorialMoment s P j =
      (Erdos1016.BoundaryDecay.eventMass s P) ^ j /
        (j.factorial : ℝ) := by
  intro j hj
  interval_cases j
  · simpa using finiteFactorialMoment_zero_eq_one s P
  · rw [finiteFactorialMoment_one_eq_eventMass]
    simp [BoundaryDecay.eventMass]



end Erdos1016.Proof.ConditionalMoments
