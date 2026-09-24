import Erdos1016

/-! The endpoint's actual type is checked independently of its axiom list.
An implication from an unproved mathematical premise cannot pass this audit. -/

set_option pp.proofs false

#print Erdos1016.Problem1016.MainTheorem
#check Erdos1016.mainTheorem
#check Erdos1016.mainTheorem_integer_excess

/- Check the expanded mathematical statement as well as its name. This
rejects accidental weakening of the definition of `MainTheorem` itself. -/
example : ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
    Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤
      (Erdos1016.Problem1016.h n : ℝ) ∧
    (Erdos1016.Problem1016.h n : ℝ) ≤
      Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus :=
  Erdos1016.mainTheorem

example : ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
    Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤
      Erdos1016.Problem1016.CommunityStatement.h n ∧
    Erdos1016.Problem1016.CommunityStatement.h n ≤
      Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus :=
  Erdos1016.mainTheorem_integer_excess

open Lean Elab Command in
run_cmd do
  let decl ← getConstInfo ``Erdos1016.mainTheorem
  unless decl.type.isConstOf ``Erdos1016.Problem1016.MainTheorem do
    throwError "The main theorem has unexpected hypotheses or conclusion"
  logInfo "ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.Problem1016.MainTheorem"

#print axioms Erdos1016.mainTheorem
#print axioms Erdos1016.mainTheorem_integer_excess
#print axioms Erdos1016.Proof.UniformCoreDecayProof.exists_uniform_core_decay
#print axioms Erdos1016.Proof.SelectedConditionalLoad.eventually_selected_conditional_load
#print axioms Erdos1016.Proof.RetainedCycleAvoidance.finite_avoidance_le
#print axioms Erdos1016.Proof.ResidualCoreCycleLoad.vertexLoad_le
#print axioms Erdos1016.Proof.CleanupConstruction.exists_cleanup_output
#print axioms Erdos1016.Proof.UniformDecayReduction.forestProbabilityBound
#print axioms Erdos1016.Problem1016.upper_bound
