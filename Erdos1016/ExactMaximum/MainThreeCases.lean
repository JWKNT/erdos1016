import Erdos1016.ExactMaximum.GirthFive.ForestProbability
import Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum

set_option autoImplicit false

/-!
# The maximum number of cycles in a graph of large rank: the three cases of the text

`Main.lean` and `MainCaps.lean` prove Theorem 1.1 of the paper "The maximum number of cycles in
a graph of large rank",

`∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`,

along the five cases of earlier texts. The text of 12 November 2026 (36 pages) has three cases
(`ThreeCases.lean`). This file proves the theorem along these three cases
(`exactMaximum_threeCases`).

* **Case 1** (a loop, or a cyclic cut of size at most three; `smallCutCaseStatement`). The method
  is that of the text: Proposition 6.3, from the theorem on few cycles for every margin.
* **Case 2** (a cycle of length at most four; `fourCycleCaseStatement`). The formal proof takes
  the vertex set of the cycle as one side of a cyclic cut of size four and applies the theorem on
  such a cut with two arbitrary sides. That theorem is proved by a limit of states, as Lemma 6.5
  of the text is. In the text one side is the cycle from the start, so the text is shorter.
* **Case 3** (girth at least five; `girthFiveCaseStatement`). The method is that of the text:
  Theorem 7.1 at girth five (`girthForestStatement_five`, file `GirthFive/ForestProbability.lean`),
  Lemma 3.2 and a connected marked set of eight vertices (`girthCaseStatement_of_forest`).

The proof does not use the case of bounded girth and not the case of large girth of the earlier
texts. `audits/ExactMaximumThreeCasesAudit.lean` checks this.

`exactMaximumStatement_of_girthFiveForest` is the same proof with Theorem 7.1 as a hypothesis.

The proofs of the parts are by Astra (`Erdos1016/ExactMaximumSupport/`) and by Fable 5.2
(`Erdos1016/ExactMaximum/`).
-/

noncomputable section

namespace Erdos1016.ExactMaximum
open CycleCount ExactMaximumSupport ExactMaximumSupport.Shortening

/-- **Case 1 of Section 8**: a loop or a cyclic cut of size at most three. -/
theorem smallCutCaseStatement : SmallCutCaseStatement :=
  smallCutCaseStatement_of_threeCut SharedSmallCut.threeCutStatement

/-- **Case 2 of Section 8**: no cyclic cut of size at most three, and a cycle of length at most
four. -/
theorem fourCycleCaseStatement : FourCycleCaseStatement :=
  fourCycleCaseStatement_of_fourCut ChainExactMaximum.fourCutStatement

/-- **Case 3 of Section 8 with the bound `2^(r-1)`**: no loop, no cyclic cut of size at most
three, and no cycle of length less than five. The proof is that of the text. -/
theorem girthCaseStatement_five : GirthCaseStatement 5 :=
  girthCaseStatement_of_forest (by norm_num) girthForestStatement_five

/-- **Case 3 of Section 8, with the bound `H(r)`.** -/
theorem girthFiveCaseStatement : GirthFiveCaseStatement :=
  girthFiveCaseStatement_of_girthCase girthCaseStatement_five

/-- **The upper bound, along the three cases of the text.** Every simple graph of large
cyclomatic number `r` has at most `H(r)` cycles. -/
theorem upperBoundStatement_threeCases : UpperBoundStatement :=
  upperBoundStatement_of_three_cases CubicReduction.cubicReductionStatement
    smallCutCaseStatement fourCycleCaseStatement girthFiveCaseStatement

/-- **Theorem 1.1 of the text, along its three cases.** -/
theorem exactMaximumStatement_threeCases : ExactMaximumStatement :=
  exactMaximumStatement_of_three_cases CubicReduction.cubicReductionStatement
    smallCutCaseStatement fourCycleCaseStatement girthFiveCaseStatement lowerBoundStatement

/-- **Theorem 1.1 of the text, written out, along its three cases.** There is `R` such that, for
every `r ≥ R`, the largest number of cycles of a simple graph with cyclomatic number `r` is the
number `H(r)` of Horak and Kim. -/
theorem exactMaximum_threeCases : ∃ R : ℕ, ∀ r, R ≤ r → maxCycles r = horakKim r :=
  exactMaximumStatement_threeCases

/-- **Equation (1.1) of the text, as printed, along its three cases.** For all large `q`:
`ψ(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q` and `ψ(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`. -/
theorem maxCycles_formula_threeCases :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      (maxCycles (2 * q + 1) : ℝ) =
          2 ^ (2 * q) + (2 * (q : ℝ) + 1 / 2) * 2 ^ q - 3 * (q : ℝ) ∧
      (maxCycles (2 * q + 2) : ℝ) =
          2 ^ (2 * q + 1) + (2 * (q : ℝ) + 9 / 2) * 2 ^ q - 3 * (q : ℝ) - 4 :=
  formula_of_exactMaximum exactMaximumStatement_threeCases

/-- **The proof of the text, with Theorem 7.1 as a hypothesis.** If the forest bound
`q(G,P) < 2/5` holds at girth five (`GirthForestStatement 5`, Theorem 7.1 of the text), then
Theorem 1.1 follows from Case 1, Case 2 and Section 8 of the text. -/
theorem exactMaximumStatement_of_girthFiveForest (h : GirthForestStatement 5) :
    ExactMaximumStatement :=
  exactMaximumStatement_of_three_cases CubicReduction.cubicReductionStatement
    smallCutCaseStatement fourCycleCaseStatement
    (girthFiveCaseStatement_of_girthCase (girthCaseStatement_of_forest (by norm_num) h))
    lowerBoundStatement

end Erdos1016.ExactMaximum
