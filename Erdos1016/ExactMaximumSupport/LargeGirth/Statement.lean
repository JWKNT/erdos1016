import Erdos1016.ExactMaximumSupport.LargeGirth.ForestProbability
import Erdos1016.ExactMaximumSupport.LargeGirth.LargeGirthCase

set_option autoImplicit false

/-!
# The unconditional large-girth case

The uniform forest bound and the actual eight-vertex marker prove Case 5.
No packing, numerical budget, or forest-probability hypothesis remains.
-/

namespace Erdos1016.ExactMaximumSupport.LargeGirth

/-- Case 5 of the eventual exact-maximum reduction. -/
theorem largeGirthStatement : ExactMaximum.LargeGirthStatement :=
  LargeGirthCase.largeGirthStatement_of_forest_bound ForestProbability.exists_cutoff

end Erdos1016.ExactMaximumSupport.LargeGirth
