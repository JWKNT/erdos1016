import Erdos1016

/-! The public theorem and the formerly missing forest estimate must be
unconditional. Expanded statements protect against a weakened target definition;
Lean's declaration-type checks separately reject hidden mathematical premises. -/
set_option pp.proofs false

#print Erdos1016.Problem1016.MainTheorem
#print Erdos1016.ShortProof.FewComponentForestEstimate
#check Erdos1016.mainTheorem
#check Erdos1016.mainTheorem_integer_excess

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
  logInfo "ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.Problem1016.MainTheorem"
  logInfo "INTEGER_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: expanded_integer_excess"
  logInfo "FOREST_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: Erdos1016.ShortProof.FewComponentForestEstimate"

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
