import Erdos1016.ExactMaximumSupport.Shortening.FourCutCompact
import Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle
import Erdos1016.ExactMaximumSupport.Shortening.BridgelessRingCase
import Erdos1016.ExactMaximumSupport.Shortening.SharedSmallCut
import Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth
import Erdos1016.ExactMaximum.Corollaries

set_option autoImplicit false

/-!
# Eventual exactness with chain packing

The arbitrary-margin cycle bound supplies both cases. Minimum-cut bridgelessness
shortens the ring classification. The short-cycle case uses one mark per
suppression and an additive bridge potential. The large-girth case uses the
new chain packing estimate in place of terminal-string packing.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum
open CycleCount

/-- The compactness four-cut proof uses direct minimum-cut bridgelessness for the ring case. -/
theorem fourCutStatement : ExactMaximum.FourCutStatement :=
  FourCutCompact.fourCutStatement_of_parts gapStatement BridgelessRingCase.ringCaseStatement

/-- Eventual exactness on the original finite-simple-graph maximum. -/
theorem exactMaximum :
    ∃ R : ℕ, ∀ r, R≤r → maxCycles r=ExactMaximum.horakKim r :=
  ExactMaximum.exactMaximumStatement_of_parts CubicReduction.cubicReductionStatement
    SharedSmallCut.threeCutStatement fourCutStatement
    PotentialShortCycle.shortCycleStatement ChainLargeGirth.largeGirthStatement
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

end Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum
