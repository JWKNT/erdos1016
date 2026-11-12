import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut

set_option autoImplicit false

/-!
# The exact maximum: the three cases of the text

The paper "The maximum number of cycles in a graph of large rank" (draft of 12 November 2026,
36 pages) proves the upper bound in three cases (its Section 8). For a connected cubic
multigraph `G` of large rank `r`:

1. `G` has a cyclic cut of size at most three (a loop gives a cut of size one): at most
   `2^(r-1) + O(2^(r/2))` cycles (Proposition 6.3);
2. `G` has no such cut, and it has a cycle of length four: a ring, with at most `H(r)` cycles,
   or fewer than `2^(r-1)` cycles (Theorem 6.6 with Corollary 6.2);
3. `G` has no such cut and no cycle of length four; then `G` has girth at least five, and it has
   fewer than `2^(r-1)` cycles (Theorem 7.1 with Lemma 3.2).

`Cases.lean` has the five cases of the earlier text. This file states the three cases and proves:

* the three cases, the reduction to cubic multigraphs and the lower bound give the theorem
  (`upperBoundStatement_of_three_cases`, `exactMaximumStatement_of_three_cases`);
* Case 1 follows from the case of a loop and from `ThreeCutStatement`
  (`smallCutCaseStatement_of_threeCut`);
* Case 2 follows from `FourCutStatement`, because a cycle of length at most four gives a cyclic
  cut of size at most four (`fourCycleCaseStatement_of_fourCut`);
* a graph without a cyclic cut of size at most three has no cycle of length at most three
  (`not_hasCycleShorterThan_four`), which is the first step of Case 3 in the text;
* Case 3, with the bound `H(r)`, follows from the cases 3, 4 and 5 of the earlier text
  (`girthFiveCaseStatement_of_cases`). This is not the proof of the text. `GirthFive.lean` has
  the reduction of Case 3 to Theorem 7.1 of the text, which has no formal proof.

In the formal Case 2 the cycle has length at most four, and in the formal Case 3 the graph has
no cycle of length at most four. So the two formal cases cover a graph without a loop and
without a cyclic cut of size at most three, as the two cases of the text do.
-/

noncomputable section

namespace Erdos1016.ExactMaximum
open CycleCount

/-- **Case 1 of Section 8.** A connected cubic multigraph of large rank `r` with a loop or with
a cyclic cut of size at most three has at most `H(r)` cycles. -/
def SmallCutCaseStatement : Prop :=
  ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic →
    R ≤ M.cycleRank → (M.HasLoop ∨ M.HasCyclicCutLE 3) →
    M.numCycles ≤ horakKim M.cycleRank

/-- **Case 2 of Section 8, Theorem 6.6 with Corollary 6.2 of the text.** A connected cubic
multigraph of large rank `r`, without a loop and without a cyclic cut of size at most three,
with a cycle of length at most four, has at most `H(r)` cycles. -/
def FourCycleCaseStatement : Prop :=
  ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 3 → M.HasCycleShorterThan 5 →
    M.numCycles ≤ horakKim M.cycleRank

/-- **Case 3 of Section 8, with the bound `H(r)`.** A connected cubic multigraph of large rank
`r`, without a loop, without a cyclic cut of size at most three and without a cycle of length at
most four, has at most `H(r)` cycles. -/
def GirthFiveCaseStatement : Prop :=
  ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 3 → ¬ M.HasCycleShorterThan 5 →
    M.numCycles ≤ horakKim M.cycleRank

/-- **The case of girth at least `D`, with the bound of the text.** A connected cubic multigraph
of large rank `r`, without a loop, without a cyclic cut of size at most three and without a
cycle of length less than `D`, has fewer than `2^(r-1)` cycles. Case 3 of the text is
`GirthCaseStatement 5`. -/
def GirthCaseStatement (D : ℕ) : Prop :=
  ∃ R : ℕ, ∀ M : FiniteMultiGraph, M.toSimpleGraph.Connected → M.IsCubic → ¬ M.HasLoop →
    R ≤ M.cycleRank → ¬ M.HasCyclicCutLE 3 → ¬ M.HasCycleShorterThan D →
    M.numCycles < 2 ^ (M.cycleRank - 1)

/-- A larger girth is a stronger hypothesis. -/
theorem GirthCaseStatement.mono {D D' : ℕ} (h : GirthCaseStatement D) (hD : D ≤ D') :
    GirthCaseStatement D' := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun M hconn hcub hloop hr hc3 hshort => hR M hconn hcub hloop hr hc3 ?_⟩
  rintro ⟨x, hx, hlen⟩
  exact hshort ⟨x, hx, lt_of_lt_of_le hlen hD⟩

/-- The bound `2^(r-1)` of the text gives the bound `H(r)`. -/
theorem girthFiveCaseStatement_of_girthCase (h : GirthCaseStatement 5) :
    GirthFiveCaseStatement := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 3, fun M hconn hcub hloop hr hc3 hshort => ?_⟩
  have hrR : R ≤ M.cycleRank := le_trans (le_max_left _ _) hr
  have hr3 : 3 ≤ M.cycleRank := le_trans (le_max_right _ _) hr
  exact (hR M hconn hcub hloop hrR hc3 hshort).le.trans (two_pow_le_horakKim _ hr3)

/-- **Case 1 from the case of a loop and from Proposition 6.3.** -/
theorem smallCutCaseStatement_of_threeCut (h3 : ThreeCutStatement) : SmallCutCaseStatement := by
  obtain ⟨K, R3, h3⟩ := h3
  refine ⟨max R3 (2 * K + 6), fun M hconn hcub hr hcase => ?_⟩
  have hr3 : R3 ≤ M.cycleRank := le_trans (le_max_left _ _) hr
  have hrK : 2 * K + 6 ≤ M.cycleRank := le_trans (le_max_right _ _) hr
  by_cases hloop : M.HasLoop
  · exact numCycles_le_horakKim_of_loop M hloop (by omega)
  · exact (h3 M hconn hcub hloop hr3 (hcase.resolve_left hloop)).trans
      (add_mul_two_pow_lt_horakKim K _ hrK).le

/-- **Case 2 from the case of a cyclic cut of size four.** In a cubic multigraph of rank at
least nine, the vertex set of a cycle of length at most four is one side of a cyclic cut of size
at most four. In the text one side of the cut is this cycle from the start. -/
theorem fourCycleCaseStatement_of_fourCut (h4 : FourCutStatement) : FourCycleCaseStatement := by
  obtain ⟨R4, h4⟩ := h4
  refine ⟨max R4 9, fun M hconn hcub hloop hr hc3 hshort => ?_⟩
  have hr4 : R4 ≤ M.cycleRank := le_trans (le_max_left _ _) hr
  have hr9 : 9 ≤ M.cycleRank := le_trans (le_max_right _ _) hr
  obtain ⟨z, hz, hlen⟩ := hshort
  have hc4 : M.HasCyclicCutLE 4 :=
    ExactMaximumSupport.ShortCycleCyclicCut.hasCyclicCutLE_four_of_rank_ge_nine M
      (M.isLoopless_iff_not_hasLoop.mpr hloop) (fun v => (hcub v).le) z hz (by omega) hr9
  exact h4 M hconn hcub hloop hr4 hc3 hc4

/-- **The first step of Case 3 in the text.** A cubic multigraph of rank at least seven, without
a loop and without a cyclic cut of size at most three, has no cycle of length at most three. -/
theorem not_hasCycleShorterThan_four (M : FiniteMultiGraph) (hcub : M.IsCubic)
    (hloop : ¬ M.HasLoop) (hr : 7 ≤ M.cycleRank) (hc3 : ¬ M.HasCyclicCutLE 3) :
    ¬ M.HasCycleShorterThan 4 := by
  rintro ⟨z, hz, hlen⟩
  exact hc3 (ExactMaximumSupport.ShortCycleCyclicCut.hasCyclicCutLE_of_cycle M
    (M.isLoopless_iff_not_hasLoop.mpr hloop) (fun v => (hcub v).le) z hz 3 (by omega) (by omega))

/-- **Case 3 with the bound `H(r)`, from the cases 3, 4 and 5 of the earlier text.** This proof
does not use the hypothesis on the girth: a cyclic cut of size four gives the bound `H(r)`, and
without such a cut the graph has a cycle shorter than the number `D` of the case of large girth,
or it has none. -/
theorem girthFiveCaseStatement_of_cases (h4 : FourCutStatement) (hS : ShortCycleStatement)
    (hL : LargeGirthStatement) : GirthFiveCaseStatement := by
  obtain ⟨R4, h4⟩ := h4
  obtain ⟨D, R5, hL⟩ := hL
  obtain ⟨RS, hS⟩ := hS D
  refine ⟨max (max R4 R5) (max RS 3), fun M hconn hcub hloop hr hc3 _ => ?_⟩
  have hr4 : R4 ≤ M.cycleRank :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr5 : R5 ≤ M.cycleRank :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hrS : RS ≤ M.cycleRank :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3 : 3 ≤ M.cycleRank :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  by_cases hc4 : M.HasCyclicCutLE 4
  · exact h4 M hconn hcub hloop hr4 hc3 hc4
  by_cases hs : M.HasCycleShorterThan D
  · exact (hS M hconn hcub hloop hrS hc4 hs).le.trans (two_pow_le_horakKim _ hr3)
  · exact (hL M hconn hcub hloop hr5 hc4 hs).le.trans (two_pow_le_horakKim _ hr3)

/-- **Section 8 of the text.** The reduction to cubic multigraphs and the three cases give the
upper bound. -/
theorem upperBoundStatement_of_three_cases (hC : CubicReductionStatement)
    (h1 : SmallCutCaseStatement) (h2 : FourCycleCaseStatement) (h3 : GirthFiveCaseStatement) :
    UpperBoundStatement := by
  obtain ⟨R1, h1⟩ := h1
  obtain ⟨R2, h2⟩ := h2
  obtain ⟨R3, h3⟩ := h3
  refine ⟨max (max R1 R2) (max R3 2), ?_⟩
  intro n G r hG hr
  have hr1 : R1 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr2 : R2 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr3 : R3 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr' : 2 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  obtain ⟨M, hconn, hcub, hrank, hle⟩ := hC n G r hG hr'
  refine hle.trans ?_
  subst hrank
  by_cases hloop : M.HasLoop
  · exact h1 M hconn hcub hr1 (Or.inl hloop)
  by_cases hc3 : M.HasCyclicCutLE 3
  · exact h1 M hconn hcub hr1 (Or.inr hc3)
  by_cases hs : M.HasCycleShorterThan 5
  · exact h2 M hconn hcub hloop hr2 hc3 hs
  · exact h3 M hconn hcub hloop hr3 hc3 hs

/-- **Theorem 1.1 of the text, as an implication from its three cases.** -/
theorem exactMaximumStatement_of_three_cases (hC : CubicReductionStatement)
    (h1 : SmallCutCaseStatement) (h2 : FourCycleCaseStatement) (h3 : GirthFiveCaseStatement)
    (hLow : LowerBoundStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_bounds (upperBoundStatement_of_three_cases hC h1 h2 h3) hLow

end Erdos1016.ExactMaximum
