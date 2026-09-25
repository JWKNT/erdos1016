import Erdos1016.Extremal.Capacity.HighCycleOutsideRank
import Erdos1016.Extremal.Recurrence.HighCycleBoundConclusion

set_option autoImplicit false

/-!
# The Section 10 rank estimate is automatic on the high-cycle branch

The canonical witness's outside-rank lower bound follows from its edge budget
and the high normalized cycle count. Consequently only the forest-probability
upper bound remains as a graph-specific input to the final recurrence.
-/

noncomputable section

namespace Erdos1016.Proof.ForestProbabilityReduction

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.FiniteGreedyStages

/-- The fixed-scale Section 10 estimate from the paper, with the rank
conjunct removed because it is proved by `canonicalWitness_outsideRank_ge`.
The constants are chosen once, and the estimate is required only for all
`R` above the resulting threshold. -/
def WitnessForestProbabilityBound : Prop :=
  ∃ C Rmin : ℕ, 8 ≤ C ∧ 5 ≤ Rmin ∧
  ∀ (R r : ℕ), Rmin ≤ R → 2 ^ (C * R ^ 4) ≤ r →
    ∀ (G : PhysicalGraph),
    G.cycleRank ≤ r →
    G.InitialCoverage (initialCapacity r) →
    2 ^ (2 * R) + 1 ≤ initialCapacity r →
    (hcovL : G.InitialCoverage (2 ^ (2 * R) + 1)) →
    tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r →
    let F := Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
      (2 ^ (2 * R) + 1) hcovL
    let E := Erdos1016.witnessSupportEdges G F
    G.outsideLinearForestProbability E ≤ (1 / 2 : ℝ) + 1 / (R : ℝ)

/-- The outside-rank conjunct in the former Section 10 interface is supplied
uniformly by the high-cycle branch hypotheses. -/
theorem highCycleBounds_of_forestProbabilityBound
    (hForest : WitnessForestProbabilityBound) :
    HighCycleBounds := by
  rcases hForest with ⟨C, Rmin, hC, hRmin, hForest⟩
  refine ⟨C, Rmin, hC, hRmin, ?_⟩
  intro R r hR hr G hGr hcov hlarge hcovL hcount
  have hprob := hForest R r hR hr G hGr hcov hlarge hcovL hcount
  change
    G.outsideLinearForestProbability
        (Erdos1016.witnessSupportEdges G
          (Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
            (2 ^ (2 * R) + 1) hcovL)) ≤ (1 / 2 : ℝ) + 1 / (R : ℝ) ∧
      2 * R ≤ G.outsideCycleRank
          (Erdos1016.witnessSupportEdges G
            (Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
              (2 ^ (2 * R) + 1) hcovL)) +
        G.commonBoundaryRank
          (Erdos1016.witnessSupportEdges G
            (Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
              (2 ^ (2 * R) + 1) hcovL))
  refine ⟨hprob, ?_⟩
  exact HighCycleOutsideRank.canonicalWitness_outsideRank_ge
    G C R r hC (by omega) hr hcount hcovL

/-- A proof of the single remaining Section 10 probability estimate yields
the complete asymptotic theorem in the project's community-standard target. -/
theorem mainTheorem_of_forestProbabilityBound
    (hForest : WitnessForestProbabilityBound) :
    Erdos1016.Problem1016.MainTheorem := by
  exact HighCycleBoundConclusion.mainTheorem_of_highCycleBounds
    (highCycleBounds_of_forestProbabilityBound hForest)

end Erdos1016.Proof.ForestProbabilityReduction
