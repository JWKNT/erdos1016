import Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap
import Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth

set_option autoImplicit false

/-!
# Eventual exactness through the shorter four-cut proof

The tree-cap theorem replaces the four-cut low-state and rank-one branches.
The fixed-marker theorem supplies the large-girth case. The other checked
cases and the actual extremal construction are reused without modification.
No previously proved exact-maximum endpoint is used.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening

/-- Every sufficiently large rank has the Horak--Kim maximum, by the alternate cases. -/
theorem exactMaximumStatement : ExactMaximum.ExactMaximumStatement :=
  ExactMaximum.exactMaximumStatement_of_parts CubicReduction.cubicReductionStatement
    ExactMaximum.threeCutStatement FourCutTreeCap.fourCutStatement
    ExactMaximum.shortCycleStatement FixedMarkerLargeGirth.largeGirthStatement
    ExactMaximum.lowerBoundStatement

/-- The complete endpoint is stated on the original maximum over finite simple graphs. -/
theorem exactMaximum :
    ∃R : ℕ,∀r,R≤r → CycleCount.maxCycles r=ExactMaximum.horakKim r :=
  exactMaximumStatement

end Erdos1016.ExactMaximumSupport.Shortening
