import Erdos1016.Extremal.Capacity.GreedyExtraction
import Erdos1016.Extremal.CapacityRecurrenceConclusion

set_option autoImplicit false

namespace Erdos1016.Proof.HighCycleBoundConclusion

open Erdos1016.Extremal
open Erdos1016.Proof.FiniteGreedyStages

/-- The fixed-scale, eventual Section 10 estimate supplies the quartic tail
recurrence and hence the full asymptotic theorem. -/
theorem mainTheorem_of_highCycleBounds
    (hSection : FiniteGreedyStages.HighCycleBounds) :
    Erdos1016.Problem1016.MainTheorem := by
  rcases hSection with ⟨C, Rmin, hC, hRmin, hBounds⟩
  have hrec : ∀ R : ℕ, Rmin ≤ R →
      tailCapacity (2 ^ (C * R ^ 4)) ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
          (2 : ℝ) ^ (2 - (R : ℝ)) := by
    intro R hR
    apply tailCapacity_quartic_recurrence_of_highCycleBounds C R hC
      (by omega)
    intro r hr G hGr hcov hlarge hcovL hcount
    exact hBounds R r hR hr G hGr hcov hlarge hcovL hcount
  exact Erdos1016.Problem1016.mainTheorem_of_quartic_tail_capacity_recurrence
    C Rmin (by omega) hrec

end Erdos1016.Proof.HighCycleBoundConclusion
