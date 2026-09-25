import Erdos1016.Extremal.Capacity.GraphWitnessComposition
import Erdos1016.Extremal.Capacity.CompositionProbability

set_option autoImplicit false

/-!
# Witness composition through the forest probability

Combines the finite graph composition bound with the common-boundary fiber
count. The local witness-support capacity is paid for by the probability that
the complementary restriction is a linear forest, up to the two pure-cycle
rank errors.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

/-- The normalized number of cycle lengths witnessed through `L` is bounded
by the witness-support `α` capacity times the complementary linear-forest
probability, plus the two explicit pure-cycle errors. -/
theorem normalized_cycleLengths_card_le_witness_forest_probability
    (G : PhysicalGraph) (F : Finset G.CycleWord) (L : ℕ)
    (witness : ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ L →
      ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      alphaCapacity L *
          G.outsideLinearForestProbability (witnessSupportEdges G F) +
        1 / (2 : ℝ) ^
          (G.outsideCycleRank (witnessSupportEdges G F) +
            G.commonBoundaryRank (witnessSupportEdges G F)) +
        1 / (2 : ℝ) ^
          (G.restrictedCycleRank (witnessSupportEdges G F) +
            G.commonBoundaryRank (witnessSupportEdges G F)) := by
  classical
  let E := witnessSupportEdges G F
  let b : ℝ := 1 / (2 : ℝ) ^
    (G.outsideCycleRank E + G.commonBoundaryRank E)
  let e : ℝ := 1 / (2 : ℝ) ^
    (G.restrictedCycleRank E + G.commonBoundaryRank E)
  have hcomp := G.normalized_cycleLengths_card_le_witness_support F L witness
  have hprob := G.complementMultiplicity_sum_normalized_le_probability_sub_baseline E
  have hα := alphaCapacity_bounds L
  have hb : 0 ≤ b := by positivity
  have hD : (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) ≠ 0 := by
    positivity
  have hlocal :
      alphaCapacity L *
          (∑ t ∈ G.activeCommonBoundaryDemands E,
            (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
            (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) ≤
        alphaCapacity L * (G.outsideLinearForestProbability E - b) := by
    have hmul := mul_le_mul_of_nonneg_left hprob hα.1
    have heq :
        alphaCapacity L *
            ((∑ t ∈ G.activeCommonBoundaryDemands E,
              (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
              (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E)) =
          alphaCapacity L *
            (∑ t ∈ G.activeCommonBoundaryDemands E,
              (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
              (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) := by
      field_simp [hD]
    rw [← heq]
    simpa [b] using hmul
  have hmain :=
    calc
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
          alphaCapacity L *
              (∑ t ∈ G.activeCommonBoundaryDemands E,
                (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
                (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
            b + e := by
        simpa [E, b, e] using hcomp
      _ ≤ alphaCapacity L *
              (G.outsideLinearForestProbability E - b) + b + e := by
        exact add_le_add_right (add_le_add_right hlocal b) e
      _ ≤ alphaCapacity L * G.outsideLinearForestProbability E + b + e := by
        nlinarith [mul_nonneg hα.1 hb]
  simpa [b, e, E] using hmain

end Erdos1016.PhysicalGraph
