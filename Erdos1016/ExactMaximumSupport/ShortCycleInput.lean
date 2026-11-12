import Erdos1016.ExactMaximum.ShortCycle
import Erdos1016.ExactMaximumSupport.CyclicShoreInput

set_option autoImplicit false

/-!
# The unconditional short-cycle case

The actual cyclic-shore theorem supplies the last input to the short-cycle count.
The gap theorem remains separate from this case.
-/
namespace Erdos1016.ExactMaximumSupport

/-- The bounded-girth case, with the cyclic-shore premise discharged. -/
theorem shortCycleStatement : ExactMaximum.ShortCycleStatement :=
  ExactMaximum.shortCycleStatement_of_shore cyclicShoreStatement

end Erdos1016.ExactMaximumSupport
