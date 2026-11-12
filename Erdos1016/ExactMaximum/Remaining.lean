import Erdos1016.ExactMaximum.LowerBound
import Erdos1016.ExactMaximum.SmallCutCase
import Erdos1016.ExactMaximum.PoleCycleBound
import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleBridges
import Erdos1016.ExactMaximum.PoleCycleCount
import Erdos1016.ExactMaximum.FourCut
import Erdos1016.ExactMaximum.ShortCycle
import Erdos1016.ExactMaximumSupport.LargeGirth.Statement
import Erdos1016.ExactMaximumSupport.PoleThinLayers
import Erdos1016.ExactMaximumSupport.CycleTwoStrands
import Erdos1016.ExactMaximumSupport.LayerMatchingInput
import Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
import Erdos1016.ExactMaximumSupport.RingCaseInput
import Erdos1016.ExactMaximumSupport.CyclicShoreInput

set_option autoImplicit false

/-!
# The exact maximum from the gap theorem

This file derives Theorem 1.1 of the paper "The maximum number of cycles in a graph of large
rank" from one statement:

* `GapStatement` (`FullPairs.lean`): Theorem 5.10, the gap theorem.

The theorem is `exactMaximumStatement_of_gap : GapStatement → ExactMaximumStatement`. The gap
theorem was the last statement to be proved (by Astra, `ExactMaximumSupport.gapStatement`).
`Main.lean` uses it and has the theorem without hypothesis.

The way to this theorem, with the statements that were open before:

* `exactMaximumStatement_of_remaining`: from `FourCutStatement` (Theorem 6.8 with
  Corollary 6.2) and `ShortCycleStatement` (Theorem 7.1);
* `fourCutStatement_of_gap_ring`: `FourCutStatement` from `GapStatement` and
  `RingCaseStatement` (four full pairs in both sides of a cut of size four give at most `H(r)`
  cycles; proved by Astra: `ExactMaximumSupport.ringCaseStatement`);
* `shortCycleStatement_of_shore`: `ShortCycleStatement` from `CyclicShoreStatement`
  (Corollary 5.6 for the pole alone; proved by Astra:
  `ExactMaximumSupport.cyclicShoreStatement`). So `shortCycleStatement` has no hypothesis.

The other parts are proved:

* the reduction to cubic multigraphs
  (`ExactMaximumSupport.CubicReduction.cubicReductionStatement`, by Astra);
* the lower bound (`lowerBoundStatement`) and the loop case;
* the cycle bound for poles (`poleCycleBoundStatement`);
* Theorem 5.4 for `ε = 1/1000` (`fewCyclesStatement`): Lemma 5.2 (a) and (b)
  (`fewCyclesStatement_of_twoPole`, `twoPoleFewCyclesStatement_of_bridgeless`), the count
  (`bridgelessFewCyclesStatement_of_layers`), Proposition 5.3
  (`ExactMaximumSupport.thinLayersStatement`, by Astra), and the two local facts about cycles
  (`ExactMaximumSupport.CycleTwoStrands.twoStrandsStatement`,
  `ExactMaximumSupport.layerMatchingStatement`, by Astra);
* Proposition 6.3 (`threeCutStatement`);
* Theorem 6.8 without the two statements about full pairs (`fourCutStatement_of_parts`): the
  structure of the cut, the count, Lemma 5.7, Lemma 6.7, and the arithmetic of Lemmas 6.5 and 6.6
  and of the four cases
  (`ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement`, by Astra);
* Theorem 7.1 without Corollary 5.6 (`shortCycleStatement_of_shore`): the shortest cycle, the
  recursion along it, the ranks and the shapes of the pieces, and the count;
* the case of large girth (`ExactMaximumSupport.LargeGirth.largeGirthStatement`, by Astra).
-/

namespace Erdos1016.ExactMaximum

/-- **Proposition 6.3 of the paper from Theorem 5.4.** The cycle bound for poles is proved
(`poleCycleBoundStatement`). -/
theorem threeCutStatement_of_fewCycles (hF : FewCyclesStatement) : ThreeCutStatement :=
  threeCutStatement_of_poles hF poleCycleBoundStatement

/-- **Theorem 5.4 of the paper for `ε = 1/1000`, from its case for connected bridgeless poles
with two ports** (Lemma 5.2). -/
theorem fewCyclesStatement_of_bridgeless (hF : BridgelessFewCyclesStatement) :
    FewCyclesStatement :=
  fewCyclesStatement_of_twoPole (twoPoleFewCyclesStatement_of_bridgeless hF)

/-- **Theorem 5.4 of the paper for `ε = 1/1000`, from the two local facts about cycles.**
Proposition 5.3 is proved (`ExactMaximumSupport.thinLayersStatement`). -/
theorem fewCyclesStatement_of_local (h2 : TwoStrandsStatement) (hM : LayerMatchingStatement) :
    FewCyclesStatement :=
  fewCyclesStatement_of_bridgeless
    (bridgelessFewCyclesStatement_of_layers ExactMaximumSupport.thinLayersStatement h2 hM)

/-- **Theorem 5.4 of the paper for `ε = 1/1000`.** A pole of rank `b` in which at least
`0.501 · 2^b` paths join two ports has at most `(K 2^b)^(1/2)` cycles. -/
theorem fewCyclesStatement : FewCyclesStatement :=
  fewCyclesStatement_of_local ExactMaximumSupport.CycleTwoStrands.twoStrandsStatement
    ExactMaximumSupport.layerMatchingStatement

/-- **Proposition 6.3 of the paper.** A connected cubic multigraph of large rank `r`, without a
loop and with a cyclic cut of size at most three, has at most `2^(r-1) + K 2^⌈r/2⌉` cycles. -/
theorem threeCutStatement : ThreeCutStatement :=
  threeCutStatement_of_fewCycles fewCyclesStatement

/-- **Theorem 1.1 from the statements that are not yet proved.** -/
theorem exactMaximumStatement_of_remaining (h4 : FourCutStatement) (hS : ShortCycleStatement) :
    ExactMaximumStatement :=
  exactMaximumStatement_of_four threeCutStatement h4 hS
    ExactMaximumSupport.LargeGirth.largeGirthStatement

/-- **Theorem 6.8 of the paper with Corollary 6.2 (Case 3), from the gap theorem and the ring
case.** A connected cubic multigraph of large rank `r`, without a loop, with a cyclic cut of
size four and without a cyclic cut of smaller size, has at most `H(r)` cycles. -/
theorem fourCutStatement_of_gap_ring (hgap : GapStatement) (hring : RingCaseStatement) :
    FourCutStatement :=
  fourCutStatement_of_parts hgap hring
    ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement fewCyclesStatement
    poleCycleBoundStatement

/-- **Theorem 1.1 from the gap theorem, the ring case and the case of a short cycle.** -/
theorem exactMaximumStatement_of_gap_ring_short (hgap : GapStatement)
    (hring : RingCaseStatement) (hS : ShortCycleStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_remaining (fourCutStatement_of_gap_ring hgap hring) hS

/-- **Theorem 1.1 from three statements about poles**: the gap theorem (Theorem 5.10), the ring
case (Case 4 of Theorem 6.8 with the upper bound of Proposition 6.1), and Corollary 5.6 for the
pole alone. -/
theorem exactMaximumStatement_of_gap_ring_shore (hgap : GapStatement)
    (hring : RingCaseStatement) (hshore : CyclicShoreStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_gap_ring_short hgap hring (shortCycleStatement_of_shore hshore)

/-- **Theorem 7.1 of the paper (Case 4).** For every `D`, a connected cubic multigraph of large
rank `r`, without a loop, without a cyclic cut of size at most four and with a cycle of length
less than `D`, has fewer than `2^(r-1)` cycles. -/
theorem shortCycleStatement : ShortCycleStatement :=
  shortCycleStatement_of_shore ExactMaximumSupport.cyclicShoreStatement

/-- **Theorem 6.8 of the paper with Corollary 6.2 (Case 3), from the gap theorem.** -/
theorem fourCutStatement_of_gap (hgap : GapStatement) : FourCutStatement :=
  fourCutStatement_of_gap_ring hgap ExactMaximumSupport.ringCaseStatement

/-- **Theorem 1.1 from the gap theorem.** Theorem 5.10 of the paper was the last statement to be
proved; `Main.lean` has the theorem without hypothesis. -/
theorem exactMaximumStatement_of_gap (hgap : GapStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_remaining (fourCutStatement_of_gap hgap) shortCycleStatement

end Erdos1016.ExactMaximum
