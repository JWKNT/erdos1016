import Erdos1016.ExactMaximum.Remaining
import Erdos1016.ExactMaximum.Corollaries
import Erdos1016.ExactMaximum.SmallCutCaps
import Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap
import Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth
import Erdos1016.ExactMaximumSupport.Shortening.MinimalCutBridgeless
import Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth

set_option autoImplicit false

/-!
# The maximum number of cycles in a graph of large rank: the proof of the shorter text

`Main.lean` has Theorem 1.1 of the paper "The maximum number of cycles in a graph of large rank":

`∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`.

This file proves the same theorem a second time, from the parts that the text of the paper uses
after 12 November 2026 (the text of 44 pages). The second proof differs from the first one in
two of the five cases:

* **The case of a cyclic cut of size four** (`fourCutStatement_caps`). The larger side `Y` of the
  cut is closed by a small tree, a *cap*, and the bound `(1/2 + o(1)) 2^r` for the number of
  cycles is applied to the result (the lemma "Cap" of the text;
  `ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound`). Then the lemmas
  "Rigidity" and "Full star", the gap theorem and the rings give the theorem. The first text had
  a lemma on poles without a pair of ports with many paths in this place, and a special case for
  a side of rank one. The proof is
  `ExactMaximumSupport.Shortening.FourCutTreeCap.fourCutStatement` (by Astra).
* **Case 5, large girth** (`largeGirthStatement_chain`). The marked set is a connected set of
  eight vertices, and the bound is `(69/160) 2^r`. The bound `q(G,P) < 2/5` of the text
  (`ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff`) uses a chain of nested
  separators two times: for the packing bound
  (`ExactMaximumSupport.Shortening.ChainPacking.exists_cutoff`) and for the two final pieces.
  The first text had a different proof of the packing bound, with sets of vertices whose parity
  equations depend on each other. The proof is
  `ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement` (by Astra).

The other parts are those of `Main.lean`: the reduction to cubic multigraphs, the lower bound,
the case of a loop, the case of a cyclic cut of size at most three (`threeCutStatement`) and the
case of bounded girth (`shortCycleStatement`).

The text also uses that the sides of a smallest cyclic cut of size four have no bridge:
`ExactMaximumSupport.Shortening.MinimalCutBridgeless.four_cut_shore_bridgeless` (by Astra). The
formal proof of the ring case does not need it.

Two more theorems are in this file for comparison. The theorems above do not use them.

* `largeGirthStatement_marker`: Case 5 with the eight marked vertices and the first proof of the
  packing bound (`ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement`).
* `threeCutStatement_caps`: the case of a cyclic cut of size at most three by caps, without the
  bound `(9/16) 2^b` for the cycles of a pole (`CutCaps.lean`, `SmallCutCaps.lean`). The text
  keeps the proof with the bound `(9/16) 2^b`, because the proof with a cap is not shorter.

The declarations of this file:

* `fourCutStatement_caps`, `largeGirthStatement_chain`: Cases 3 and 5;
* `upperBoundStatement_caps`: every simple graph of large cyclomatic number `r` has at most
  `H(r)` cycles;
* `exactMaximumStatement_caps`, `exactMaximum_caps`: Theorem 1.1;
* `maxCycles_formula_caps`: equation (1.1), for odd and for even rank;
* `largeGirthStatement_marker`, `threeCutStatement_caps`: for comparison.
-/

noncomputable section

namespace Erdos1016.ExactMaximum

open CycleCount

/-- **The case of a cyclic cut of size four, with the rings (Case 3), by the cap.** The proof is
in `Erdos1016/ExactMaximumSupport/Shortening/` (by Astra). -/
theorem fourCutStatement_caps : FourCutStatement :=
  ExactMaximumSupport.Shortening.FourCutTreeCap.fourCutStatement

/-- **Case 5 of the paper, with a connected set of eight vertices and the chain of separators.**
The proof is in `Erdos1016/ExactMaximumSupport/Shortening/` (by Astra). -/
theorem largeGirthStatement_chain : LargeGirthStatement :=
  ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement

/-- **The upper bound, by the cases of the text.** Every simple graph of large cyclomatic number
`r` has at most `H(r)` cycles. -/
theorem upperBoundStatement_caps : UpperBoundStatement :=
  upperBoundStatement_of_cases ExactMaximumSupport.CubicReduction.cubicReductionStatement
    threeCutStatement fourCutStatement_caps shortCycleStatement largeGirthStatement_chain

/-- **Theorem 1.1 of the paper, by the cases of the text.** -/
theorem exactMaximumStatement_caps : ExactMaximumStatement :=
  exactMaximumStatement_of_parts ExactMaximumSupport.CubicReduction.cubicReductionStatement
    threeCutStatement fourCutStatement_caps shortCycleStatement largeGirthStatement_chain
    lowerBoundStatement

/-- **Theorem 1.1 of the paper, written out, by the cases of the text.** There is `R` such that,
for every `r ≥ R`, the largest number of cycles of a simple graph with cyclomatic number `r` is
the number `H(r)` of Horak and Kim. -/
theorem exactMaximum_caps : ∃ R : ℕ, ∀ r, R ≤ r → maxCycles r = horakKim r :=
  exactMaximumStatement_caps

/-- **Equation (1.1) of the paper, as printed, by the cases of the text.** For all large `q`:
`ψ(2q+1) = 2^(2q) + (2q + 1/2) 2^q - 3q` and `ψ(2q+2) = 2^(2q+1) + (2q + 9/2) 2^q - 3q - 4`. -/
theorem maxCycles_formula_caps :
    ∃ Q : ℕ, ∀ q, Q ≤ q →
      (maxCycles (2 * q + 1) : ℝ) =
          2 ^ (2 * q) + (2 * (q : ℝ) + 1 / 2) * 2 ^ q - 3 * (q : ℝ) ∧
      (maxCycles (2 * q + 2) : ℝ) =
          2 ^ (2 * q + 1) + (2 * (q : ℝ) + 9 / 2) * 2 ^ q - 3 * (q : ℝ) - 4 :=
  formula_of_exactMaximum exactMaximumStatement_caps

/-- **Case 5 with the first proof of the packing bound.** For comparison; the theorems above use
`largeGirthStatement_chain`. -/
theorem largeGirthStatement_marker : LargeGirthStatement :=
  ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement

/-- **The case of a cyclic cut of size at most three, by caps.** A connected cubic multigraph of
large rank `r`, without a loop and with a cyclic cut of size at most three, has at most
`2^(r-1) + K 2^⌈r/2⌉` cycles. This proof does not use the bound `(9/16) 2^b` for the cycles of a
pole. The text and the theorems above use `threeCutStatement`. -/
theorem threeCutStatement_caps : ThreeCutStatement :=
  threeCutStatement_of_caps fewCyclesStatement capStatement

end Erdos1016.ExactMaximum
