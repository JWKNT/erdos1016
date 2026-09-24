import Erdos1016.Extremal.Capacity.CycleCountComposition
import Erdos1016.Extremal.Capacity.WitnessAlpha

set_option autoImplicit false

/-!
# Composition bound for a short-cycle witness partition

For the actual edge support of a finite family witnessing all short cycle
lengths, the local multiplicity term in the graph composition inequality is
bounded by the community `alphaCapacity`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PhysicalGraph

/-- Apply the numerical composition bound to the edge partition given by a
short-cycle witness support. -/
theorem normalized_cycleLengths_card_le_witness_support
    (G : PhysicalGraph) (F : Finset G.CycleWord) (L : ℕ)
    (witness : ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ L →
      ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      alphaCapacity L *
        (∑ t ∈ G.activeCommonBoundaryDemands (witnessSupportEdges G F),
          (G.restrictedLinearForestMultiplicity
            (witnessSupportEdges G F)ᶜ t : ℝ)) /
          (2 : ℝ) ^
            (G.outsideCycleRank (witnessSupportEdges G F) +
              G.commonBoundaryRank (witnessSupportEdges G F)) +
      1 / (2 : ℝ) ^
        (G.outsideCycleRank (witnessSupportEdges G F) +
          G.commonBoundaryRank (witnessSupportEdges G F)) +
      1 / (2 : ℝ) ^
        (G.restrictedCycleRank (witnessSupportEdges G F) +
          G.commonBoundaryRank (witnessSupportEdges G F)) := by
  let E := witnessSupportEdges G F
  have hμA : ∀ t ∈ G.activeCommonBoundaryDemands E,
      (G.restrictedLinearForestMultiplicity E t : ℝ) ≤
        (2 : ℝ) ^ G.restrictedCycleRank E * alphaCapacity L := by
    intro t _
    exact G.restrictedMultiplicity_le_alpha_of_witnessFamily F L witness t
  have h := G.normalized_cycleLengths_card_le_partition E
    (alphaCapacity L) hμA
  simpa [E] using h

end Erdos1016.PhysicalGraph
