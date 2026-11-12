import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle
import Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap
import Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth

set_option autoImplicit false

/-! Eventual exactness with the direct bounded-port replacement of Section 7. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.BoundedPortExactMaximum

/-- The actual maximum over finite simple graphs, with the bounded-port path
bound used throughout the short-cycle case. No old exactness endpoint is used. -/
theorem exactMaximum :
    ∃R : ℕ,∀r,R≤r → CycleCount.maxCycles r=ExactMaximum.horakKim r :=
  ExactMaximum.exactMaximumStatement_of_parts CubicReduction.cubicReductionStatement
    ExactMaximum.threeCutStatement FourCutTreeCap.fourCutStatement
    BoundedPortShortCycle.shortCycleStatement FixedMarkerLargeGirth.largeGirthStatement
    ExactMaximum.lowerBoundStatement

end Erdos1016.ExactMaximumSupport.Shortening.BoundedPortExactMaximum
