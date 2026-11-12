import Erdos1016.ExactMaximum.Remaining
import Erdos1016.ExactMaximum.Corollaries
import Erdos1016.ExactMaximumSupport.GapInput

set_option autoImplicit false

/-!
# The maximum number of cycles in a graph of large rank: the theorem

This file has Theorem 1.1 of the paper "The maximum number of cycles in a graph of large rank"
without hypothesis:

`exactMaximum : ∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`.

`CycleCount.maxCycles r` is the largest number of cycles of a simple graph with cyclomatic
number `r` (`Erdos1016/CycleCount/Asymptotic.lean`), and `horakKim r` is the number `H(r)` of
Horak and Kim (`HorakKim.lean`).

The proof has six parts (`Cases.lean`): the reduction to cubic multigraphs, the lower bound, and
four cases for a connected cubic multigraph without loops. `Remaining.lean` derives the theorem
from the gap theorem (Theorem 5.10 of the paper), which was the last open statement. Astra
proved it: `ExactMaximumSupport.gapStatement`. `README.md` in this folder says who proved which
part.

The declarations of this file:

* `gapStatement`, `fourCutStatement`: Theorem 5.10, and Theorem 6.8 with Corollary 6.2;
* `upperBoundStatement`: every simple graph of large cyclomatic number `r` has at most `H(r)`
  cycles;
* `exactMaximumStatement`, `exactMaximum`: Theorem 1.1;
* `maxCycles_parity`, `maxCycles_formula`: equation (1.1), for odd and for even rank;
* `maxCycles_secondOrder`, `maxCycles_secondOrder_explicit`: `ψ(r) - 2^(r-1) = Θ(r 2^(r/2))`,
  with the constants `1/8` and `2`.
-/

noncomputable section

namespace Erdos1016.ExactMaximum

open CycleCount Filter Asymptotics

/-- **Theorem 5.10 of the paper (the gap).** In a pole of rank `b`, the number of paths between
two ports is `2^b` or at most `(15/16) 2^b`. The proof is in `Erdos1016/ExactMaximumSupport/`
(by Astra). -/
theorem gapStatement : GapStatement :=
  ExactMaximumSupport.gapStatement

/-- **Theorem 6.8 of the paper with Corollary 6.2 (Case 3).** A connected cubic multigraph of
large rank `r`, without a loop, with a cyclic cut of size four and without a cyclic cut of
smaller size, has at most `H(r)` cycles. -/
theorem fourCutStatement : FourCutStatement :=
  fourCutStatement_of_gap gapStatement

/-- **The upper bound.** Every simple graph of large cyclomatic number `r` has at most `H(r)`
cycles. -/
theorem upperBoundStatement : UpperBoundStatement :=
  upperBoundStatement_of_cases ExactMaximumSupport.CubicReduction.cubicReductionStatement
    threeCutStatement fourCutStatement shortCycleStatement
    ExactMaximumSupport.LargeGirth.largeGirthStatement

/-- **Theorem 1.1 of the paper.** -/
theorem exactMaximumStatement : ExactMaximumStatement :=
  exactMaximumStatement_of_gap gapStatement

/-- **Theorem 1.1 of the paper, written out.** There is `R` such that, for every `r ≥ R`, the
largest number of cycles of a simple graph with cyclomatic number `r` is the number `H(r)` of
Horak and Kim. -/
theorem exactMaximum : ∃ R : ℕ, ∀ r, R ≤ r → maxCycles r = horakKim r :=
  exactMaximumStatement

/-- **Equation (1.1) of the paper, without subtraction.** For all large `q`:
`ψ(2q+1) + 3q = 2^(2q) + (4q+1) 2^(q-1)` and `ψ(2q+2) + 3q + 4 = 2^(2q+1) + (4q+9) 2^(q-1)`. -/
theorem maxCycles_parity :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      maxCycles (2 * q + 1) + 3 * q = 2 ^ (2 * q) + (4 * q + 1) * 2 ^ (q - 1) ∧
      maxCycles (2 * q + 2) + 3 * q + 4 = 2 ^ (2 * q + 1) + (4 * q + 9) * 2 ^ (q - 1) :=
  parity_of_exactMaximum exactMaximumStatement

/-- **Equation (1.1) of the paper, as printed.** For all large `q`:
`ψ(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q` and `ψ(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`. -/
theorem maxCycles_formula :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      (maxCycles (2 * q + 1) : ℝ) =
          2 ^ (2 * q) + (2 * (q : ℝ) + 1 / 2) * 2 ^ q - 3 * (q : ℝ) ∧
      (maxCycles (2 * q + 2) : ℝ) =
          2 ^ (2 * q + 1) + (2 * (q : ℝ) + 9 / 2) * 2 ^ q - 3 * (q : ℝ) - 4 :=
  formula_of_exactMaximum exactMaximumStatement

/-- **The second term.** `ψ(r) - 2^(r-1) = Θ(r 2^(r/2))`. -/
theorem maxCycles_secondOrder :
    (fun r : ℕ => (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) :=
  secondOrder_of_exactMaximum exactMaximumStatement

/-- **The second term with explicit constants.** For all large `r`:
`r 2^(r/2) / 8 ≤ ψ(r) - 2^(r-1) ≤ 2 r 2^(r/2)`. -/
theorem maxCycles_secondOrder_explicit :
    ∃ R : ℕ, ∀ r, R ≤ r →
      (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2) / 8 ≤ (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ∧
      (maxCycles r : ℝ) - (2 : ℝ) ^ (r - 1) ≤ 2 * ((r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) :=
  secondOrder_explicit_of_exactMaximum exactMaximumStatement

end Erdos1016.ExactMaximum
