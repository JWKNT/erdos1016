import Erdos1016.ExactMaximum.Main
import Erdos1016.ExactMaximum.MainCaps
import Lean

/-!
# Audit of the second proof of the exact maximum

Run: `lake env lean audits/ExactMaximumCapsAudit.lean`.

The file checks three things for `Erdos1016.ExactMaximum.exactMaximum_caps`, the second proof of
Theorem 1.1 of the paper "The maximum number of cycles in a graph of large rank":

1. the exact types of the new declarations;
2. their axioms (`#print axioms`);
3. that the second proof does not use the declarations that the text no longer uses: the
   arithmetic of the first proof of the case of a cyclic cut of size four, the first proof of
   Case 5, the first proof of the packing bound (sets of vertices whose parity equations depend
   on each other), and the first proof of Theorem 1.1. The command `#assert_not_used` follows all
   constants in the types and in the proof terms; it fails with an error if a listed declaration
   occurs.

The same check for `threeCutStatement_caps`: the case of a cyclic cut of size at most three by
caps does not use the bound `(9/16) 2^b` for the cycles of a pole.

The last commands are controls: the first proof `exactMaximum` and the comparison theorem
`largeGirthStatement_marker` do use these declarations.
-/

open Lean Elab Command

namespace CapsAudit

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

end CapsAudit

open Erdos1016 Erdos1016.ExactMaximum

/-! ### 1. Types -/

example : ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r := exactMaximum_caps
example : ExactMaximumStatement := exactMaximumStatement_caps
example : UpperBoundStatement := upperBoundStatement_caps
example : ThreeCutStatement := threeCutStatement_caps
example : FourCutStatement := fourCutStatement_caps
example : LargeGirthStatement := largeGirthStatement_chain
example : LargeGirthStatement := largeGirthStatement_marker
example : CapStatement := capStatement
example : FewCyclesStatement → CapStatement → ThreeCutStatement := threeCutStatement_of_caps

#check @CapTwoWith
#check @CapThreeWith
#check @ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound
#check @ExactMaximumSupport.Shortening.MinimalCutBridgeless.four_cut_shore_bridgeless
#check @maxCycles_formula_caps
#check @ExactMaximumSupport.Shortening.ChainPacking.exists_cutoff
#check @ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff
#check @Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared

/-! ### 2. Axioms -/

#print axioms capStatement
#print axioms threeCutStatement_of_caps
#print axioms threeCutStatement_caps
#print axioms fourCutStatement_caps
#print axioms largeGirthStatement_chain
#print axioms largeGirthStatement_marker
#print axioms ExactMaximumSupport.Shortening.ChainPacking.exists_cutoff
#print axioms ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff
#print axioms Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared
#print axioms upperBoundStatement_caps
#print axioms exactMaximumStatement_caps
#print axioms exactMaximum_caps
#print axioms maxCycles_formula_caps
#print axioms ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound
#print axioms ExactMaximumSupport.Shortening.MinimalCutBridgeless.four_cut_shore_bridgeless

/-! ### 3. Declarations that the second proof does not use -/

#assert_not_used Erdos1016.ExactMaximum.exactMaximum_caps
  [Erdos1016.ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement,
   Erdos1016.ExactMaximum.fourCutStatement_of_parts,
   Erdos1016.ExactMaximum.fourCutStatement,
   Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximum.largeGirthStatement_marker,
   Erdos1016.ExactMaximumSupport.LargeGirth.Packing.exists_cutoff,
   Erdos1016.ExactMaximumSupport.LargeGirth.Packing.exists_finset_cutoff,
   Erdos1016.ExactMaximum.exactMaximumStatement_of_gap,
   Erdos1016.ExactMaximum.exactMaximumStatement,
   Erdos1016.ExactMaximum.exactMaximum,
   Erdos1016.ExactMaximum.threeCutStatement_caps,
   Erdos1016.mainTheorem]

#assert_not_used Erdos1016.ExactMaximum.maxCycles_formula_caps
  [Erdos1016.ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement,
   Erdos1016.ExactMaximum.exactMaximum]

#assert_not_used Erdos1016.ExactMaximum.threeCutStatement_caps
  [Erdos1016.ExactMaximum.poleCycleBoundStatement,
   Erdos1016.ExactMaximum.numCycles_le_of_large_rank,
   Erdos1016.ExactMaximum.threeCutStatement_of_poles,
   Erdos1016.ExactMaximum.threeCutStatement]

/-! ### Control: the first proof uses them -/

#assert_all_used Erdos1016.ExactMaximum.exactMaximum
  [Erdos1016.ExactMaximum.poleCycleBoundStatement,
   Erdos1016.ExactMaximum.numCycles_le_of_large_rank,
   Erdos1016.ExactMaximum.threeCutStatement_of_poles,
   Erdos1016.ExactMaximum.threeCutStatement,
   Erdos1016.ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement,
   Erdos1016.ExactMaximum.fourCutStatement_of_parts,
   Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximum.exactMaximumStatement_of_gap]

#assert_all_used Erdos1016.ExactMaximum.largeGirthStatement_marker
  [Erdos1016.ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.LargeGirth.Packing.exists_finset_cutoff]

/-! ### The parts that the second proof uses -/

#assert_all_used Erdos1016.ExactMaximum.exactMaximum_caps
  [Erdos1016.ExactMaximum.threeCutStatement,
   Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap.fourCutStatement,
   Erdos1016.ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound,
   Erdos1016.ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement,
   Erdos1016.ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff,
   Erdos1016.ExactMaximumSupport.Shortening.ChainPacking.exists_finset_cutoff,
   Erdos1016.ExactMaximum.shortCycleStatement,
   Erdos1016.ExactMaximum.lowerBoundStatement]
