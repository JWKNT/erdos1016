import Erdos1016.ExactMaximumSupport.Shortening.FourCutCompact
import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle
import Erdos1016.ExactMaximum.MainCaps

set_option autoImplicit false

/-!
# Eventual exactness through bounded ports, caps, and compactness

This assembly uses the direct bounded-port short-cycle case, the actual
compactness four-cut case, the two/three-cut caps, and the fixed marker case.
No earlier exact-maximum theorem is a proof input.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.CompactExactMaximum
open CycleCount

/-- Eventual exactness on the original finite-simple-graph maximum. -/
theorem exactMaximum :
    ∃ R : ℕ, ∀ r, R≤r → maxCycles r=ExactMaximum.horakKim r :=
  ExactMaximum.exactMaximumStatement_of_parts CubicReduction.cubicReductionStatement
    ExactMaximum.threeCutStatement_caps FourCutCompact.fourCutStatement
    BoundedPortShortCycle.shortCycleStatement FixedMarkerLargeGirth.largeGirthStatement
    ExactMaximum.lowerBoundStatement

/-- Both parity formulas follow from this new proof of eventual exactness. -/
theorem maxCycles_formula :
    ∃ Q : ℕ, ∀ q, Q≤q →
      (maxCycles (2*q+1) : ℝ)=
        2^(2*q)+(2*(q:ℝ)+1/2)*2^q-3*(q:ℝ) ∧
      (maxCycles (2*q+2) : ℝ)=
        2^(2*q+1)+(2*(q:ℝ)+9/2)*2^q-3*(q:ℝ)-4 :=
  ExactMaximum.formula_of_exactMaximum exactMaximum

/-- The same assembly gives the sharp second-order term with explicit constants. -/
theorem secondOrder_explicit :
    ∃ R : ℕ, ∀ r, R≤r →
      (r:ℝ)*(2:ℝ)^((r:ℝ)/2)/8≤(maxCycles r:ℝ)-(2:ℝ)^(r-1) ∧
      (maxCycles r:ℝ)-(2:ℝ)^(r-1)≤2*((r:ℝ)*(2:ℝ)^((r:ℝ)/2)) :=
  ExactMaximum.secondOrder_explicit_of_exactMaximum exactMaximum

end Erdos1016.ExactMaximumSupport.Shortening.CompactExactMaximum
