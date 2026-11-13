import Erdos1016.ExactMaximum.Main
import Erdos1016.ExactMaximum.MainCaps
import Erdos1016.ExactMaximum.MainThreeCases
import Lean

/-!
# Audit of the proof of the exact maximum along the three cases of the text

Run: `lake env lean audits/ExactMaximumThreeCasesAudit.lean`.

The paper "The maximum number of cycles in a graph of large rank" (draft of 12 November 2026,
36 pages) has three cases. `Erdos1016/ExactMaximum/MainThreeCases.lean` proves Theorem 1.1 along
these cases (`exactMaximum_threeCases`). The third case uses Theorem 7.1 of the text at girth
five, `girthForestStatement_five` (`Erdos1016/ExactMaximum/GirthFive/ForestProbability.lean`).
This file checks:

1. the exact types of the declarations;
2. their axioms (`#print axioms`);
3. which declarations each proof uses. The command `#assert_not_used` follows all constants in
   the types and in the proof terms; it fails with an error if a listed declaration occurs. The
   command `#assert_all_used` fails if a listed declaration does not occur.

The third check shows three facts.

* `exactMaximum_threeCases` uses no earlier proof of Theorem 1.1, not the case of bounded girth
  and not the case of large girth of the earlier texts.
* It uses the proof of Theorem 7.1 at girth five and the parts of that proof: the rail lemma,
  the bound for two terminals, the lemma on a region with slabs, the pieces at girth five, the
  two blocks, the packing bound of the first family, the packing bound at large girth for the
  later families (with the pieces at large girth), and the last step of the proof for large
  girth.
* `exactMaximumStatement_of_girthFiveForest` is the same proof with Theorem 7.1 as a hypothesis.
-/

open Lean Elab Command

namespace ThreeCasesAudit

/-- All constants that `root` uses, directly or through other declarations (types and proof
terms). -/
def usedConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    if let some ci := env.find? n then
      for d in ci.type.getUsedConstants do
        unless visited.contains d do
          stack := stack.push d
      if let some v := ci.value? then
        for d in v.getUsedConstants do
          unless visited.contains d do
            stack := stack.push d
  return visited

/-- The listed declarations that `root` uses. -/
def usedAmong (root : Ident) (names : Array Ident) : CommandElabM (Name × Nat × Nat × Array Name) := do
  let env ← getEnv
  let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let used := usedConstants env rootName
  let all := used.toList
  let project := all.filter fun n => (`Erdos1016).isPrefixOf n
  let mut hits : Array Name := #[]
  for n in names do
    let nm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    if used.contains nm then
      hits := hits.push nm
  return (rootName, all.length, project.length, hits)

/-- `#assert_not_used root [a, b, …]` fails if the declaration `root` uses one of `a, b, …`. -/
elab "#assert_not_used " root:ident " [" names:ident,* "]" : command => do
  let (rootName, total, project, hits) ← usedAmong root names.getElems
  unless hits.isEmpty do
    throwError "{rootName} uses {hits}"
  logInfo m!"{rootName} uses {total} declarations, {project} of them in this project, and none of the {names.getElems.size} listed declarations"

/-- `#assert_all_used root [a, b, …]` fails if the declaration `root` does not use all of
`a, b, …`. -/
elab "#assert_all_used " root:ident " [" names:ident,* "]" : command => do
  let (rootName, total, project, hits) ← usedAmong root names.getElems
  unless hits.size = names.getElems.size do
    throwError "{rootName} uses only {hits}"
  logInfo m!"{rootName} uses {total} declarations, {project} of them in this project, and all of the {names.getElems.size} listed declarations"

end ThreeCasesAudit

open Erdos1016 Erdos1016.ExactMaximum

/-! ### 1. Types -/

example : ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r := exactMaximum_threeCases
example : ExactMaximumStatement := exactMaximumStatement_threeCases
example : UpperBoundStatement := upperBoundStatement_threeCases
example : SmallCutCaseStatement := smallCutCaseStatement
example : FourCycleCaseStatement := fourCycleCaseStatement
example : GirthFiveCaseStatement := girthFiveCaseStatement
example : GirthForestStatement 5 → ExactMaximumStatement :=
  exactMaximumStatement_of_girthFiveForest
example : GirthForestStatement 5 := girthForestStatement_five
example : GirthCaseStatement 5 := girthCaseStatement_five
example : CubicReductionStatement → SmallCutCaseStatement → FourCycleCaseStatement →
    GirthFiveCaseStatement → UpperBoundStatement := upperBoundStatement_of_three_cases
example : ThreeCutStatement → SmallCutCaseStatement := smallCutCaseStatement_of_threeCut
example : FourCutStatement → FourCycleCaseStatement := fourCycleCaseStatement_of_fourCut
example : GirthForestStatement 5 → GirthCaseStatement 5 :=
  girthCaseStatement_of_forest (by norm_num)
example : GirthCaseStatement 5 → GirthFiveCaseStatement := girthFiveCaseStatement_of_girthCase

#check @GirthForestStatement
#check @numCycles_le_marked
#check @three_le_cut_of_no_cyclic_cut
#check @not_hasCycleShorterThan_four
#check @girthCaseStatement_of_forest
#check @maxCycles_formula_threeCases

/-! ### 2. Axioms -/

#print axioms numCycles_le_marked
#print axioms three_le_cut_of_no_cyclic_cut
#print axioms not_hasCycleShorterThan_four
#print axioms girthCaseStatement_of_forest
#print axioms upperBoundStatement_of_three_cases
#print axioms smallCutCaseStatement
#print axioms fourCycleCaseStatement
#print axioms girthFiveCaseStatement
#print axioms girthForestStatement_five
#print axioms girthCaseStatement_five
#print axioms GirthFive.rail_bound
#print axioms GirthFive.two_terminal_card_le
#print axioms GirthFive.two_terminal_region
#print axioms GirthFive.region_not_rigid
#print axioms GirthFive.window_not_rigid
#print axioms GirthFive.affine_forest_density_le_prod
#print axioms GirthFive.exists_affine_bound_girth_five
#print axioms GirthFive.exists_block_bound
#print axioms GirthFive.exists_base_finset_packing
#print axioms GirthFive.shifted_size_bound
#print axioms upperBoundStatement_threeCases
#print axioms exactMaximumStatement_threeCases
#print axioms exactMaximum_threeCases
#print axioms maxCycles_formula_threeCases
#print axioms exactMaximumStatement_of_girthFiveForest

/-! ### 3. Which declarations the proofs use -/

/- The proof along the three cases uses no earlier proof of Theorem 1.1, and neither the case of
bounded girth nor the case of large girth. -/
#assert_not_used Erdos1016.ExactMaximum.exactMaximum_threeCases
  [Erdos1016.ExactMaximum.exactMaximumStatement,
   Erdos1016.ExactMaximum.exactMaximum,
   Erdos1016.ExactMaximum.exactMaximumStatement_caps,
   Erdos1016.ExactMaximum.exactMaximum_caps,
   Erdos1016.ExactMaximum.upperBoundStatement_of_cases,
   Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum.exactMaximum,
   Erdos1016.mainTheorem,
   Erdos1016.ExactMaximum.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff,
   Erdos1016.ExactMaximum.girthFiveCaseStatement_of_cases]

/- Its parts. -/
#assert_all_used Erdos1016.ExactMaximum.exactMaximum_threeCases
  [Erdos1016.ExactMaximum.upperBoundStatement_of_three_cases,
   Erdos1016.ExactMaximumSupport.CubicReduction.cubicReductionStatement,
   Erdos1016.ExactMaximum.lowerBoundStatement,
   Erdos1016.ExactMaximumSupport.Shortening.SharedSmallCut.threeCutStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum.fourCutStatement,
   Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness.exists_tolerance,
   Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut.hasCyclicCutLE_four_of_rank_ge_nine,
   Erdos1016.ExactMaximum.girthCaseStatement_of_forest,
   Erdos1016.ExactMaximum.numCycles_le_marked,
   Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker.exists_eight,
   Erdos1016.ExactMaximum.girthForestStatement_five]

/- The parts of Theorem 7.1 at girth five. -/
#assert_all_used Erdos1016.ExactMaximum.girthForestStatement_five
  [Erdos1016.ExactMaximum.GirthFive.rail_bound,
   Erdos1016.ExactMaximum.GirthFive.no_rail,
   Erdos1016.ExactMaximum.GirthFive.two_terminal_card_le,
   Erdos1016.ExactMaximum.GirthFive.two_terminal_region,
   Erdos1016.ExactMaximum.GirthFive.exists_word_two_terminals,
   Erdos1016.ExactMaximum.GirthFive.region_not_rigid,
   Erdos1016.ExactMaximum.GirthFive.window_not_rigid,
   Erdos1016.ExactMaximum.GirthFive.affine_forest_density_le_prod,
   Erdos1016.ExactMaximum.GirthFive.exists_affine_bound_girth_five,
   Erdos1016.Probability.PoleMarker.exists_supported_demand_layer_bound,
   Erdos1016.ExactMaximum.GirthFive.exists_block_bound,
   Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct.region_product,
   Erdos1016.ExactMaximum.GirthFive.exists_row_bound,
   Erdos1016.ExactMaximumSupport.Shortening.DisjointRegionChain.exists_clean_chain_blocks,
   Erdos1016.ExactMaximum.GirthFive.exists_base_finset_packing,
   Erdos1016.ExactMaximumSupport.Shortening.ChainPacking.exists_finset_cutoff,
   Erdos1016.ExactMaximum.GirthFive.shifted_size_bound,
   Erdos1016.ExactMaximumSupport.Shortening.LargeOrderPieces.exists_constant,
   Erdos1016.ExactMaximumSupport.Shortening.LargeOrderChain.bound_of_budgets]

/- Theorem 7.1 at girth five uses no case statement and no earlier forest bound for large
girth as a whole. -/
#assert_not_used Erdos1016.ExactMaximum.girthForestStatement_five
  [Erdos1016.ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff,
   Erdos1016.ExactMaximumSupport.Shortening.ChainRaisedGirth.exists_raising_cutoff,
   Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainExactMaximum.fourCutStatement,
   Erdos1016.ExactMaximumSupport.Shortening.SharedSmallCut.threeCutStatement]

/- The proof from Theorem 7.1 as a hypothesis does not use the proof of Theorem 7.1. -/
#assert_not_used Erdos1016.ExactMaximum.exactMaximumStatement_of_girthFiveForest
  [Erdos1016.ExactMaximum.girthForestStatement_five,
   Erdos1016.ExactMaximum.GirthFive.exists_affine_bound_girth_five,
   Erdos1016.ExactMaximum.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle.shortCycleStatement,
   Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff,
   Erdos1016.ExactMaximumSupport.Shortening.ChainPacking.exists_cutoff,
   Erdos1016.ExactMaximum.girthFiveCaseStatement,
   Erdos1016.ExactMaximum.girthFiveCaseStatement_of_cases,
   Erdos1016.ExactMaximum.exactMaximum,
   Erdos1016.ExactMaximum.exactMaximum_caps,
   Erdos1016.ExactMaximum.exactMaximum_threeCases]

/- Its parts: the first two cases, Lemma 3.2 and the marked set of eight vertices. -/
#assert_all_used Erdos1016.ExactMaximum.exactMaximumStatement_of_girthFiveForest
  [Erdos1016.ExactMaximum.upperBoundStatement_of_three_cases,
   Erdos1016.ExactMaximum.smallCutCaseStatement,
   Erdos1016.ExactMaximum.fourCycleCaseStatement,
   Erdos1016.ExactMaximum.girthCaseStatement_of_forest,
   Erdos1016.ExactMaximum.numCycles_le_marked,
   Erdos1016.ExactMaximum.three_le_cut_of_no_cyclic_cut,
   Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker.exists_eight,
   Erdos1016.ExactMaximumSupport.CubicReduction.cubicReductionStatement,
   Erdos1016.ExactMaximum.lowerBoundStatement]
