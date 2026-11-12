import Erdos1016.ExactMaximum.LoopCase
import Erdos1016.ExactMaximum.Statement

set_option autoImplicit false

/-!
# The exact maximum: reduction to five cases

This file is the formal counterpart of Section 9 of the paper "The maximum number of cycles in a
graph of large rank". It states the results that Section 9 combines, as propositions about
connected cubic multigraphs, and it proves that they imply the upper bound and the theorem.

Proved in the repository without hypotheses:

* Case 1, a multigraph with a loop (`numCycles_le_horakKim_of_loop`).

Stated here and not yet proved:

* `CubicReductionStatement` (Lemma 3.10 of the paper);
* `ThreeCutStatement` (Proposition 6.3);
* `FourCutStatement` (Theorem 6.8 with Corollary 6.2);
* `ShortCycleStatement` (Theorem 7.1);
* `LargeGirthStatement` (Theorem 8.1 with the count in Case 5 of Section 9);
* `LowerBoundStatement` (the rings of Horak and Kim, Corollary 6.2).

So the theorems of this file are implications. They do not yet give the exact maximum.
-/

noncomputable section

namespace Erdos1016.ExactMaximum
open CycleCount

/-- **Lemma 3.10 of the paper**, in the direction that the upper bound needs: every simple graph
of cyclomatic number `r ≥ 2` has at most as many cycles as some connected cubic multigraph of
cycle rank `r`. -/
def CubicReductionStatement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → 2 ≤ r →
    ∃ M : FiniteMultiGraph, M.toSimpleGraph.Connected ∧ M.IsCubic ∧ M.cycleRank = r ∧
      numCycles G ≤ M.numCycles

/-- **Case 1.** A multigraph with a loop and cycle rank `r ≥ 3` has at most `H(r)` cycles. -/
theorem numCycles_le_horakKim_of_loop (M : FiniteMultiGraph) (h : M.HasLoop)
    (hr : 3 ≤ M.cycleRank) : M.numCycles ≤ horakKim M.cycleRank :=
  (M.numCycles_le_of_loop h).trans (two_pow_le_horakKim _ hr)

/-- **Case 2, Proposition 6.3 of the paper.** A connected cubic multigraph without loops, of
large cycle rank `r`, with a cyclic cut of at most three edges has at most
`2^(r-1) + K * 2^(r/2)` cycles. The exponent `(r+1)/2` is the rounded-up half of `r`. -/
def ThreeCutStatement : Prop :=
  ∃ K R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → M.HasCyclicCutLE 3 →
    M.numCycles ≤ 2 ^ (M.cycleRank - 1) + K * 2 ^ ((M.cycleRank + 1) / 2)

/-- **Case 3, Theorem 6.8 with Corollary 6.2 of the paper.** A connected cubic multigraph without
loops, of large cycle rank `r`, with a cyclic cut of four edges and no smaller cyclic cut has at
most `H(r)` cycles. In the paper it is a ring, with at most `H(r)` cycles, or it has fewer than
`2^(r-1)` cycles. -/
def FourCutStatement : Prop :=
  ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 3 → M.HasCyclicCutLE 4 →
    M.numCycles ≤ horakKim M.cycleRank

/-- **Case 4, Theorem 7.1 of the paper.** For every `D`, a connected cubic multigraph without
loops, of large cycle rank `r`, without a cyclic cut of at most four edges and with a cycle of
length less than `D` has fewer than `2^(r-1)` cycles. -/
def ShortCycleStatement : Prop :=
  ∀ D : ℕ, ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic →
    ¬ M.HasLoop → R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 4 → M.HasCycleShorterThan D →
    M.numCycles < 2 ^ (M.cycleRank - 1)

/-- **Case 5, from Theorem 8.1 of the paper.** There is `D` such that a connected cubic
multigraph without loops, of large cycle rank `r`, without a cyclic cut of at most four edges
and without a cycle of length less than `D` has fewer than `2^(r-1)` cycles. -/
def LargeGirthStatement : Prop :=
  ∃ D R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 4 → ¬ M.HasCycleShorterThan D →
    M.numCycles < 2 ^ (M.cycleRank - 1)

/-- **Section 9 of the paper.** The reduction to cubic multigraphs and the cases 2 to 5 give the
upper bound. Case 1 is proved above. -/
theorem upperBoundStatement_of_cases (hC : CubicReductionStatement) (h3 : ThreeCutStatement)
    (h4 : FourCutStatement) (hS : ShortCycleStatement) (hL : LargeGirthStatement) :
    UpperBoundStatement := by
  obtain ⟨K, R3, h3⟩ := h3
  obtain ⟨R4, h4⟩ := h4
  obtain ⟨D, R5, hL⟩ := hL
  obtain ⟨RS, hS⟩ := hS D
  refine ⟨max (max (max R3 R4) (max R5 RS)) (2 * K + 6), ?_⟩
  intro n G r hG hr
  have hr3 : R3 ≤ r :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hr
  have hr4 : R4 ≤ r :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hr
  have hr5 : R5 ≤ r :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hr
  have hrS : RS ≤ r :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hr
  have hrK : 2 * K + 6 ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨M, hconn, hcub, hrank, hle⟩ := hC n G r hG (by omega)
  refine hle.trans ?_
  subst hrank
  by_cases hloop : M.HasLoop
  · exact numCycles_le_horakKim_of_loop M hloop (by omega)
  by_cases hc3 : M.HasCyclicCutLE 3
  · exact (h3 M hconn hcub hloop hr3 hc3).trans
      (add_mul_two_pow_lt_horakKim K _ hrK).le
  by_cases hc4 : M.HasCyclicCutLE 4
  · exact h4 M hconn hcub hloop hr4 hc3 hc4
  by_cases hs : M.HasCycleShorterThan D
  · exact (hS M hconn hcub hloop hrS hc4 hs).le.trans (two_pow_le_horakKim _ (by omega))
  · exact (hL M hconn hcub hloop hr5 hc4 hs).le.trans (two_pow_le_horakKim _ (by omega))

/-- **Theorem 1.1 of the paper, as an implication.** The six statements above give the exact
maximum. -/
theorem exactMaximumStatement_of_parts (hC : CubicReductionStatement) (h3 : ThreeCutStatement)
    (h4 : FourCutStatement) (hS : ShortCycleStatement) (hL : LargeGirthStatement)
    (hLow : LowerBoundStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_bounds (upperBoundStatement_of_cases hC h3 h4 hS hL) hLow

end Erdos1016.ExactMaximum
