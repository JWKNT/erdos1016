import Erdos1016.ExactMaximumSupport.MixedCappedMarkedCounts
import Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction

set_option autoImplicit false

/-!
# The unconditional full-pair gap

All marked physical labels in the capped ladder satisfy the required count.
The checked reduction transfers these counts through suppression and bridges.
-/
namespace Erdos1016.ExactMaximumSupport

/-- The full-pair gap, with all concrete marked-count cases discharged. -/
theorem gapStatement : ExactMaximum.GapStatement :=
  ThirdPortCappedReduction.gapStatement_of_capped
    MixedCappedMarkedCounts.cappedMarkedCountStatement

end Erdos1016.ExactMaximumSupport
