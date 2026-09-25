import Erdos1016.Extremal.Capacity.LowCycleCountBound

set_option autoImplicit false

/-!
# Reduction of the quartic tail recurrence to its missing branch

The small-coverage and low-cycle-count cases already give the desired
pointwise estimate. This module packages the complementary case for an
extremal realizer, isolating the graph estimate still needed for the §10
recurrence.
-/

noncomputable section
namespace Erdos1016.Extremal

/-- At every rank on the quartic scale, either the desired pointwise
near-halving estimate holds, or an extremal realizer has both large initial
coverage and at least half the tail capacity worth of normalized distinct
cycle lengths. Thus the only unresolved case in the recurrence is explicit.
-/
theorem quartic_pointwise_or_large_cycle_branch
    (C R r : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hr : 2 ^ (C * R ^ 4) ≤ r) :
    initialCapacityExcess r ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
          (2 : ℝ) ^ (2 - (R : ℝ)) ∨
      ∃ G : PhysicalGraph,
        G.cycleRank ≤ r ∧
        G.InitialCoverage (initialCapacity r) ∧
        2 ^ (2 * R) + 1 ≤ initialCapacity r ∧
        tailCapacity R / 2 ≤
          (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r := by
  obtain ⟨G, hGr, hcov⟩ := exists_initialCapacity_realizer r
  by_cases hsmallCoverage : initialCapacity r < 2 ^ (2 * R) + 1
  · exact Or.inl (initialCapacityExcess_le_error_of_quartic_small_coverage
      C R r hC hR hr hsmallCoverage |>.trans (by
        have hnonneg : 0 ≤ ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R := by
          have hcoeff : 0 ≤ (1 / 2 : ℝ) + 1 / (R : ℝ) := by positivity
          exact mul_nonneg hcoeff (tailCapacity_bounds R).1
        linarith))
  · have hlargeCoverage : 2 ^ (2 * R) + 1 ≤ initialCapacity r := by omega
    by_cases hsmallCount :
        (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r < tailCapacity R / 2
    · have hlow := low_cycle_count_forces_capacity_bound R r hR G hcov hsmallCount
      exact Or.inl (by
        have hnonneg : 0 ≤ (2 : ℝ) ^ (2 - (R : ℝ)) := by positivity
        linarith)
    · exact Or.inr ⟨G, hGr, hcov, hlargeCoverage, le_of_not_gt hsmallCount⟩

end Erdos1016.Extremal
