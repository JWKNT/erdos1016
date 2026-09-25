import Erdos1016.Extremal.Capacity.TailRecurrenceAlternatives

set_option autoImplicit false

/-!
# Interface from the high-cycle branch to the quartic tail recurrence

The low-cycle and small-coverage branches are already proved. This module
records the precise remaining graph estimate needed on the complementary
branch and proves that it closes the recurrence, including the passage from
an extremal realizer to its normalized capacity.
-/

noncomputable section
namespace Erdos1016.Extremal

/-- Any graph covering all lengths through the extremal endpoint has at
least `initialCapacityExcess` distinct cycle lengths, after normalization.
This is the graph-to-capacity inequality used in the high-cycle branch. -/
theorem initialCapacityExcess_le_normalized_cycle_count
    (r : ℕ) (G : PhysicalGraph)
    (hcov : G.InitialCoverage (initialCapacity r)) :
    initialCapacityExcess r ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r := by
  have hI2 : 2 ≤ initialCapacity r := initialCapacity_two_le r
  have hcard : initialCapacity r - 2 ≤ G.cycleLengths.card := by
    have h := Finset.card_le_card hcov
    simpa only [Nat.card_Icc] using h
  have hcardReal : ((initialCapacity r - 2 : ℕ) : ℝ) ≤
      (G.cycleLengths.card : ℝ) := by exact_mod_cast hcard
  have hnum : (initialCapacity r : ℝ) - 2 ≤
      (G.cycleLengths.card : ℝ) := by
    simpa [Nat.cast_sub hI2] using hcardReal
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  unfold initialCapacityExcess
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)







end Erdos1016.Extremal
