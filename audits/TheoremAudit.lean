import Erdos1016

/-! The public theorem and the formerly missing forest estimate must be
unconditional. Expanded statements protect against a weakened target definition;
Lean's declaration-type checks separately reject hidden mathematical premises. -/
set_option pp.proofs false

#print Erdos1016.Problem1016.MainTheorem
#print Erdos1016.ShortProof.FewComponentForestEstimate
#check Erdos1016.mainTheorem
#check Erdos1016.mainTheorem_integer_excess
#print Erdos1016.CycleCount.cycleEdgeSets
#print Erdos1016.CycleCount.numCycles
#print Erdos1016.CycleCount.CycleCountStatement
#print Erdos1016.CycleCount.GeneralCycleCountStatement
#print Erdos1016.CycleCount.cycleCounts
#print Erdos1016.CycleCount.maxCycles
#print Erdos1016.CycleCount.AsymptoticCycleCount
#check Erdos1016.cycleCountTheorem
#check Erdos1016.cycleCountTheorem_general
#check Erdos1016.cycleCountAsymptotic

example : ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
    Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤
      (Erdos1016.Problem1016.h n : ℝ) ∧
    (Erdos1016.Problem1016.h n : ℝ) ≤
      Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus :=
  Erdos1016.mainTheorem

namespace Erdos1016.TheoremAudit

/-- Independent spelling of the community statement with integer excess. -/
def IntegerStatement : Prop :=
  ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
    Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤
      Erdos1016.Problem1016.CommunityStatement.h n ∧
    Erdos1016.Problem1016.CommunityStatement.h n ≤
      Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus

example : IntegerStatement := Erdos1016.mainTheorem_integer_excess

/-- Independent spelling of the cycle-count bound. A cycle is counted once,
by the edge set of a Mathlib cycle walk. The number `r` is the cyclomatic
number `edges - vertices + components`. -/
def CycleStatement : Prop :=
  ∃ r₁ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    ((({s : Set (Sym2 (Fin n)) | ∃ (v : Fin n) (p : G.Walk v v),
        p.IsCycle ∧ s = {a | a ∈ p.edges}}).ncard : ℕ) : ℝ) ≤
      (1 / 2 + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) * 2 ^ r

example : CycleStatement := Erdos1016.cycleCountTheorem

/-- The same bound on every finite vertex type. -/
def GeneralCycleStatement : Prop :=
  ∃ r₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (r : ℕ),
    r + Fintype.card V = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    ((({s : Set (Sym2 V) | ∃ (v : V) (p : G.Walk v v),
        p.IsCycle ∧ s = {a | a ∈ p.edges}}).ncard : ℕ) : ℝ) ≤
      (1 / 2 + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) * 2 ^ r

example : GeneralCycleStatement := Erdos1016.cycleCountTheorem_general

/-- Independent spelling of the asymptotic statement: the largest number of
cycles at cyclomatic number `r`, divided by `2^r`, tends to `1/2`. -/
def AsymptoticStatement : Prop :=
  Filter.Tendsto (fun r : ℕ =>
    ((sSup {c : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent ∧
        ({s : Set (Sym2 (Fin n)) | ∃ (v : Fin n) (p : G.Walk v v),
          p.IsCycle ∧ s = {a | a ∈ p.edges}}).ncard = c} : ℕ) : ℝ) / 2 ^ r)
    Filter.atTop (nhds (1 / 2))

example : AsymptoticStatement := Erdos1016.cycleCountAsymptotic

open Lean Elab Command in
run_cmd do
  let decl ← getConstInfo ``Erdos1016.mainTheorem
  unless decl.type.isConstOf ``Erdos1016.Problem1016.MainTheorem do
    throwError "The main theorem has unexpected hypotheses or conclusion"
  let forest ← getConstInfo ``Erdos1016.ShortProof.fewComponentForestEstimate
  unless forest.type.isConstOf ``Erdos1016.ShortProof.FewComponentForestEstimate do
    throwError "The forest estimate has unexpected hypotheses or conclusion"
  let integer ← getConstInfo ``Erdos1016.mainTheorem_integer_excess
  liftTermElabM do
    unless ← Lean.Meta.isDefEq integer.type (mkConst ``IntegerStatement) do
      throwError "The integer theorem has unexpected hypotheses or conclusion"
  let cycles ← getConstInfo ``Erdos1016.cycleCountTheorem
  unless cycles.type.isConstOf ``Erdos1016.CycleCount.CycleCountStatement do
    throwError "The cycle-count theorem has unexpected hypotheses or conclusion"
  let asymptotic ← getConstInfo ``Erdos1016.cycleCountAsymptotic
  unless asymptotic.type.isConstOf ``Erdos1016.CycleCount.AsymptoticCycleCount do
    throwError "The asymptotic cycle-count theorem has unexpected hypotheses or conclusion"
  let general ← getConstInfo ``Erdos1016.cycleCountTheorem_general
  unless general.type.isConstOf ``Erdos1016.CycleCount.GeneralCycleCountStatement do
    throwError "The general cycle-count theorem has unexpected hypotheses or conclusion"
  liftTermElabM do
    unless ← Lean.Meta.isDefEq general.type (mkConst ``GeneralCycleStatement) do
      throwError "The general cycle-count theorem differs from its expanded statement"
    unless ← Lean.Meta.isDefEq cycles.type (mkConst ``CycleStatement) do
      throwError "The cycle-count theorem differs from its expanded statement"
    unless ← Lean.Meta.isDefEq asymptotic.type (mkConst ``AsymptoticStatement) do
      throwError "The asymptotic cycle-count theorem differs from its expanded statement"
  logInfo "ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.Problem1016.MainTheorem"
  logInfo "INTEGER_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: expanded_integer_excess"
  logInfo "FOREST_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.ShortProof.FewComponentForestEstimate"
  logInfo "CYCLE_COUNT_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.CycleCount.CycleCountStatement"
  logInfo "CYCLE_ASYMPTOTIC_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.CycleCount.AsymptoticCycleCount"

end Erdos1016.TheoremAudit

#print axioms Erdos1016.mainTheorem
#print axioms Erdos1016.mainTheorem_integer_excess
#print axioms Erdos1016.ShortProof.fewComponentForestEstimate
#print axioms Erdos1016.ShortProof.eventually_marked_forest_bound
#print axioms Erdos1016.ShortProof.eventually_exists_retained_cycle_supply
#print axioms Erdos1016.FiniteMultiGraph.InducedSimpleRealization.actual_cycle_links_le
#print axioms Erdos1016.FiniteMultiGraph.InducedCycleAvoidance.forest_le_half_add_twenty
#print axioms Erdos1016.FiniteMultiGraph.SeedFamilyAvoidance.second_moment_le
#print axioms Erdos1016.FiniteMultiGraph.InducedSimpleRealization.cycleSeed_injective
#print axioms Erdos1016.ShortProof.mainTheorem_of_few_component_forest_estimate
#print axioms Erdos1016.ShortProof.exists_budgeted_witness
#print axioms Erdos1016.ShortProof.coverageDensity_le_outsideForest
#print axioms Erdos1016.ShortProof.actualRankTail_le_of_connected
#print axioms Erdos1016.Extremal.LinearExponentialDecay.recurrence_logStar_bound
#print axioms Erdos1016.ExceptionalPartners.multigraph_three_links_card_le_cut
#print axioms Erdos1016.Nonbacktracking.DeficitTrace.normalized_even_trace_lower
#print axioms Erdos1016.Proof.LowDegreeTraceCycles.cycleWordMass_ge_log_ratio
#print axioms Erdos1016.Proof.DeficitCutoffParameters.eventually_rank_cycleWordMass_ge
#print axioms Erdos1016.Proof.ExceptionalLoadCutoffs.eventually_cutoff_exceptional_load_le_quarter
#print axioms Erdos1016.Proof.LowDegreeVertexMass.cycle_mass_at_vertex_le
#print axioms Erdos1016.BoundaryDecay.small_cut_event_bound
#print axioms Erdos1016.FiniteMultiGraph.order_add_two_eq_twice_rank_add_marked_deficit
#print axioms Erdos1016.FiniteMultiGraph.loopCycleSpaceEquiv
#print axioms Erdos1016.FiniteMultiGraph.average_normalizedSeedIndicator
#print axioms Erdos1016.PackingCover.mass_le_of_packing
#print axioms Erdos1016.Problem1016.upper_bound

#print axioms Erdos1016.FiniteMultiGraph.smallCut_forest_bound
#print axioms Erdos1016.FiniteMultiGraph.DisjointRegionCuts.exceptional_partner_card_le
#print axioms Erdos1016.LinkCorrelation.multigraph_zeroCut_pair
#print axioms Erdos1016.FiniteMultiGraph.ConnectedContraction.project_surjective
#print axioms Erdos1016.FiniteMultiGraph.regionCycleEvent_pair_density
#print axioms Erdos1016.FiniteMultiGraph.isForestWord_iff_no_even_support
#print axioms Erdos1016.ShortProof.IncidencePaths.outsideForestProbability_le_region
#print axioms Erdos1016.ShortProof.CycleCore.networkCycleEquiv
#print axioms Erdos1016.ShortProof.CycleCore.cycleRank_preserved
#print axioms Erdos1016.Proof.ExteriorTreePathCount.card_exterior_trees_le_length_blocks
#print axioms Erdos1016.FiniteMultiGraph.ExteriorComponents.card_le_marked_large_cyclic_blocks
#print axioms Erdos1016.BoundaryDecay.exceptional_row_le_of_packing

#print axioms Erdos1016.ShortProof.exists_marked_subcubic_reduction
#print axioms Erdos1016.ShortProof.fewComponentForestEstimate_of_marked_bound
#print axioms Erdos1016.FiniteMultiGraph.exists_short_region_packing
#print axioms Erdos1016.FiniteMultiGraph.retained_no_loops
#print axioms Erdos1016.FiniteMultiGraph.retained_simple
#print axioms Erdos1016.Proof.RetainedSizeBounds.eventually_retained_size_and_deficit
#print axioms Erdos1016.Proof.ForestCutoffParameters.eventually_geometry_cutoffs
#print axioms Erdos1016.Proof.ForestCutoffParameters.link_error_le_envelope
#print axioms Erdos1016.FiniteMultiGraph.ExteriorComponents.smallCyclicPart_card_le

#print axioms Erdos1016.cycleCountTheorem
#print axioms Erdos1016.cycleCountTheorem_general
#print axioms Erdos1016.cycleCountAsymptotic
#print axioms Erdos1016.CycleCount.cycleCountBound_of_forestEstimate
#print axioms Erdos1016.CycleCount.cycleCountStatement_of_bound
#print axioms Erdos1016.CycleCount.asymptoticCycleCount_of_statement
#print axioms Erdos1016.CycleCount.generalCycleCountStatement_of_statement
#print axioms Erdos1016.CycleCount.card_cycleWord_le
#print axioms Erdos1016.CycleCount.exists_triangle_family
#print axioms Erdos1016.CycleCount.exists_independent_edges
#print axioms Erdos1016.CycleCount.cycleRank_addChords_le
#print axioms Erdos1016.CycleCount.exists_graph_many_cycles
