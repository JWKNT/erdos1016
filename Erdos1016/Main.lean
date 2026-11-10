import Erdos1016.Probability.Avoidance.FewComponentForest
import Erdos1016.Extremal.MinimumEdgesStatement
import Erdos1016.CycleCount.FiniteTypes
import Erdos1016.ExactCounting.NoWaste

set_option autoImplicit false

namespace Erdos1016

/-- Erdős problem 1016: the minimum excess of a pancyclic simple graph on
`n` vertices is `log₂ n + log* n + O(1)`, uniformly for every `n ≥ 3`. -/
theorem mainTheorem : Problem1016.MainTheorem := by
  exact ShortProof.mainTheorem_of_few_component_forest_estimate
    ShortProof.fewComponentForestEstimate

/-- The same theorem with excess defined in the integers as the minimum
number of edges minus the number of vertices. -/
theorem mainTheorem_integer_excess :
    ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
      Real.logb 2 (n : ℝ) + (Extremal.logStar n : ℝ) - Aminus ≤
        Problem1016.CommunityStatement.h n ∧
      Problem1016.CommunityStatement.h n ≤
        Real.logb 2 (n : ℝ) + (Extremal.logStar n : ℝ) + Aplus :=
  Problem1016.mainTheorem_community_statement.mp mainTheorem

/-- The number of cycles: every simple graph on `Fin n` with large cyclomatic
number `r` has at most `(1/2 + 21 / log₂ log₂ log₂ r) * 2^r` cycles. -/
theorem cycleCountTheorem : CycleCount.CycleCountStatement :=
  CycleCount.cycleCountStatement_of_bound
    (CycleCount.cycleCountBound_of_forestEstimate ShortProof.fewComponentForestEstimate)

/-- The cycle-count bound for simple graphs on every finite vertex type. -/
theorem cycleCountTheorem_general : CycleCount.GeneralCycleCountStatement :=
  CycleCount.generalCycleCountStatement_of_statement cycleCountTheorem

/-- The maximum number of cycles of a simple graph with cyclomatic number `r`
is asymptotically `2^(r-1)`. -/
theorem cycleCountAsymptotic : CycleCount.AsymptoticCycleCount :=
  CycleCount.asymptoticCycleCount_of_statement cycleCountTheorem

/-- A connected simple graph with cyclomatic number `r` has at most `2^r` paths
between two vertices. If it has exactly `2^r`, then each of these paths has at
least `r` edges, and the graph without the edges of any one of them is
acyclic. -/
theorem twoTerminalTheorem : ExactCounting.TwoTerminalStatement :=
  ExactCounting.twoTerminalStatement

/-- If every outside part of a subgraph `W` is the outside part of a cycle,
then the graph without the edges of `W` has no two edge-disjoint cycles, and
the cyclomatic numbers satisfy `β(G) ≤ β(W) + |V(W)| + 3`. -/
theorem noWasteTheorem : ExactCounting.NoWasteStatement :=
  ExactCounting.noWasteStatement

end Erdos1016
