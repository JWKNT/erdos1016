import Erdos1016.Probability.Avoidance.UniformCoreDecay
import Erdos1016.Extremal.Recurrence.UniformDecayReduction
import Erdos1016.Extremal.MinimumEdgesStatement

set_option autoImplicit false

namespace Erdos1016

/-- Erdős problem 1016: the minimum excess of a pancyclic simple graph on
`n` vertices is `log₂ n + log* n + O(1)`, uniformly for every `n ≥ 3`. -/
theorem mainTheorem : Problem1016.MainTheorem := by
  obtain ⟨N₀, hdecay⟩ := Proof.UniformCoreDecayProof.exists_uniform_core_decay
  exact Proof.UniformDecayReduction.mainTheorem (by norm_num) hdecay

/-- The same theorem with excess defined in the integers as the minimum
number of edges minus the number of vertices. -/
theorem mainTheorem_integer_excess :
    ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
      Real.logb 2 (n : ℝ) + (Extremal.logStar n : ℝ) - Aminus ≤
        Problem1016.CommunityStatement.h n ∧
      Problem1016.CommunityStatement.h n ≤
        Real.logb 2 (n : ℝ) + (Extremal.logStar n : ℝ) + Aplus :=
  Problem1016.mainTheorem_community_statement.mp mainTheorem

end Erdos1016
