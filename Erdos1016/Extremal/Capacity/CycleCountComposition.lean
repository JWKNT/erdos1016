import Erdos1016.Extremal.Capacity.CycleLengthCount
import Erdos1016.Extremal.Capacity.ComplementRank

set_option autoImplicit false

/-!
# Graph instantiation of the finite composition inequality

This module substitutes the cycle count decomposition and the edge-partition
rank identity into the numerical composition estimate. The sole unproved
capacity input is kept explicit as a per-demand envelope on one side.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PhysicalGraph

/-- The cycle count across a physical edge partition, normalized by the host
cycle-space size, is bounded by the one-side capacity envelope and the two
pure-cycle error terms. `hμA` is the local-capacity estimate required from
the remaining recurrence argument. -/
theorem normalized_cycleLengths_card_le_partition
    (G : PhysicalGraph) (E : Finset G.Edge) (a : ℝ)
    (hμA : ∀ t ∈ G.activeCommonBoundaryDemands E,
      (G.restrictedLinearForestMultiplicity E t : ℝ) ≤
        (2 : ℝ) ^ G.restrictedCycleRank E * a) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      a * (∑ t ∈ G.activeCommonBoundaryDemands E,
        (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
          (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
        1 / (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
        1 / (2 : ℝ) ^ (G.restrictedCycleRank E + G.commonBoundaryRank E) := by
  classical
  let U := G.activeCommonBoundaryDemands E
  let μA : G.Demand → ℕ := G.restrictedLinearForestMultiplicity E
  let μM : G.Demand → ℕ := G.restrictedLinearForestMultiplicity Eᶜ
  let pureA : ℕ := (G.pureCycleLengths E).card
  let pureM : ℕ := (G.pureCycleLengths Eᶜ).card
  let r : ℕ := G.cycleRank
  let rA : ℕ := G.restrictedCycleRank E
  let rM : ℕ := G.outsideCycleRank E
  let d : ℕ := G.commonBoundaryRank E
  have hrank : r = rA + rM + d := by
    dsimp [r, rA, rM, d]
    exact G.cycleRank_edgePartition E
  have hpureA : pureA ≤ 2 ^ rA - 1 := by
    exact G.pureCycleLengths_card_le E
  have hpureM : pureM ≤ 2 ^ rM - 1 := by
    dsimp [pureM, rM]
    rw [G.outsideCycleRank_eq_restrictedCycleRank_compl E]
    exact G.pureCycleLengths_card_le Eᶜ
  have hμ : ∀ t ∈ U, (μA t : ℝ) ≤ (2 : ℝ) ^ rA * a := by
    intro t ht
    exact hμA t (by simpa [U] using ht)
  have hcomposition := Capacity.normalized_finite_composition
    U r rA rM d pureA pureM μA μM a hrank hpureA hpureM hμ
  have hcount :
      (G.cycleLengths.card : ℝ) ≤
        (pureA : ℝ) + pureM +
          ∑ t ∈ U, (μA t : ℝ) * (μM t : ℝ) := by
    have hn := G.cycleLengths_card_le_partition E
    exact_mod_cast hn
  apply (div_le_div_of_nonneg_right hcount (by positivity)).trans
  simpa [r, rA, rM, d, U, μM] using hcomposition

end Erdos1016.PhysicalGraph
