import Erdos1016.Main
import Erdos1016.ExactMaximum.MainThreeCases

/-!
# Entry module for the maximum number of cycles

Text: "The maximum number of cycles in a graph of large rank" (`paper/minimal/exact-maximum/`).

This module imports the formal proof of the main theorem along the three cases of the text. It
does not import `Erdos1016/ExactMaximum/Main.lean` and `MainCaps.lean`, the proofs along the
five cases of earlier texts. Its import closure has 662 of the 686 modules of the library, and
the proof uses 529 of them (`Erdos1016/README.md`): the files of Astra with the parts are
imported as a whole, and some of them contain other proofs of the theorem.

| Text | Declaration |
|---|---|
| Theorem 1.1: `ψ(r) = H(r)` for all large `r` | `Erdos1016.ExactMaximum.exactMaximum_threeCases` |
| Equation (1.1): the two formulas of Horak and Kim | `Erdos1016.ExactMaximum.maxCycles_formula_threeCases` |
| Corollary 3.3: `ψ(r) ~ 2^(r-1)` | `Erdos1016.cycleCountAsymptotic` |
| Section 8, Case 1 (a loop or a cyclic cut of size at most three) | `Erdos1016.ExactMaximum.smallCutCaseStatement` |
| Section 8, Case 2 (a cycle of length at most four) | `Erdos1016.ExactMaximum.fourCycleCaseStatement` |
| Section 8, Case 3 (girth at least five) | `Erdos1016.ExactMaximum.girthFiveCaseStatement` |
| Theorem 7.1: `q(G,P) < 2/5` at girth five | `Erdos1016.ExactMaximum.girthForestStatement_five` |
| Lemma 3.2: cycles and a marked set | `Erdos1016.ExactMaximum.numCycles_le_marked` |
| The lower bound (the ring of squares) | `Erdos1016.ExactMaximum.lowerBoundStatement` |

`Erdos1016/ExactMaximum/README.md` has the table statement by statement, and
`audits/ExactMaximumThreeCasesAudit.lean` checks which declarations the proof uses.
`Erdos1016/ExactMaximum/Main.lean` and `MainCaps.lean` and the files `*ExactMaximum.lean` of
`Erdos1016/ExactMaximumSupport/Shortening/` have other proofs of the theorem, along the five
cases of earlier texts.
-/
