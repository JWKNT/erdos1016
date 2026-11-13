import Erdos1016
import Lean

/-!
# Which modules does each endpoint theorem use?

Run: `lake env lean audits/UsageMap.lean`.

For each of five groups of endpoint theorems the command `#usage_map` follows all constants in
the types and in the proof terms, and it records the module of every constant of this project.
It prints two tables in Markdown:

1. for every folder of `Erdos1016/`, the number of its modules and the number of modules that
   each group uses;
2. for every module of `Erdos1016/ExactMaximum/`, the groups that use it.

The groups:

* `F`: the forest estimate (`ShortProof.eventually_marked_forest_bound_logSquared`,
  `ShortProof.fewComponentForestEstimate_logSquared`);
* `P`: the pancyclic theorem (`mainTheorem`);
* `T`: the maximum number of cycles along the three cases of the text
  (`ExactMaximum.exactMaximum_threeCases`, `ExactMaximum.maxCycles_formula_threeCases`,
  `cycleCountAsymptotic`);
* `M`: the maximum number of cycles along the five cases (`ExactMaximum.exactMaximum`);
* `C`: the same with caps (`ExactMaximum.exactMaximum_caps`).

`Erdos1016/README.md` has a copy of the first table, and `Erdos1016/ExactMaximum/README.md` a
copy of the second.
-/

open Lean Elab Command

namespace UsageMap

/-- All constants that the roots use, directly or through other declarations. -/
def usedConstants (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots
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

/-- The folder of a module of this project, as it is shown in the tables. -/
def folderOf (m : Name) : String :=
  match m.components with
  | [_, _] => "*.lean"
  | [_, a, _] =>
    if a == `ExactMaximumSupport || a == `ExactMaximum then a.toString ++ "/*.lean"
    else a.toString ++ "/"
  | _ :: a :: b :: _ =>
    if a == `ExactMaximumSupport || a == `ExactMaximum then
      a.toString ++ "/" ++ b.toString ++ "/"
    else a.toString ++ "/"
  | _ => m.toString

/-- The modules of this project that the roots use. -/
def usedModules (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let used := usedConstants env roots
  let mut mods : NameSet := {}
  for n in used.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`Erdos1016).isPrefixOf m then
        mods := mods.insert m
  return mods

elab "#usage_map" : command => do
  let env ← getEnv
  let groups : Array (String × Array Name) := #[
    ("F", #[`Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared,
            `Erdos1016.ShortProof.fewComponentForestEstimate_logSquared]),
    ("P", #[`Erdos1016.mainTheorem]),
    ("T", #[`Erdos1016.ExactMaximum.exactMaximum_threeCases,
            `Erdos1016.ExactMaximum.maxCycles_formula_threeCases,
            `Erdos1016.cycleCountAsymptotic]),
    ("M", #[`Erdos1016.ExactMaximum.exactMaximum]),
    ("C", #[`Erdos1016.ExactMaximum.exactMaximum_caps])]
  for (_, roots) in groups do
    for r in roots do
      unless env.contains r do
        throwError "unknown declaration {r}"
  let sets := groups.map fun (_, roots) => usedModules env roots
  let all := (env.header.moduleNames.filter fun m =>
    (`Erdos1016).isPrefixOf m && m != `Erdos1016).qsort (fun a b => a.toString < b.toString)
  -- the first table: folders
  let mut folders : Array String := #[]
  for m in all do
    let f := folderOf m
    unless folders.contains f do
      folders := folders.push f
  let mut out := "| Folder | Modules | " ++ " | ".intercalate (groups.map (·.1)).toList ++ " |\n"
  out := out ++ "|---|---|" ++ String.join (groups.map fun _ => "---|").toList ++ "\n"
  let mut totals : Array Nat := groups.map fun _ => 0
  for f in folders do
    let ms := all.filter fun m => folderOf m == f
    let mut row := "| `" ++ f ++ "` | " ++ toString ms.size ++ " |"
    for i in [0:groups.size] do
      let c := (ms.filter fun m => sets[i]!.contains m).size
      totals := totals.modify i (· + c)
      row := row ++ " " ++ toString c ++ " |"
    out := out ++ row ++ "\n"
  let mut last := "| **all** | " ++ toString all.size ++ " |"
  for i in [0:groups.size] do
    last := last ++ " " ++ toString totals[i]! ++ " |"
  out := out ++ last ++ "\n"
  logInfo m!"{out}"
  -- the second table: the modules of `ExactMaximum/`
  let mut out2 := "| Module | " ++ " | ".intercalate (groups.map (·.1)).toList ++ " |\n"
  out2 := out2 ++ "|---|" ++ String.join (groups.map fun _ => "---|").toList ++ "\n"
  for m in all do
    if (`Erdos1016.ExactMaximum).isPrefixOf m then
      let mut row := "| `" ++ (m.toString.drop "Erdos1016.ExactMaximum.".length) ++ "` |"
      for i in [0:groups.size] do
        row := row ++ (if sets[i]!.contains m then " x |" else "  |")
      out2 := out2 ++ row ++ "\n"
  logInfo m!"{out2}"

end UsageMap

#usage_map
