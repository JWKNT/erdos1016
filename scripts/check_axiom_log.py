#!/usr/bin/env python3
"""Validate the statement marker and the complete set of kernel axiom reports."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGET = "Erdos1016.Problem1016.MainTheorem"
FOREST_TARGET = "Erdos1016.ShortProof.FewComponentForestEstimate"
STATUS = f"ENDPOINT_STATUS: UNCONDITIONAL; TARGET: {TARGET}"
INTEGER_STATUS = "INTEGER_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: expanded_integer_excess"
FOREST_STATUS = f"FOREST_ENDPOINT_STATUS: UNCONDITIONAL; TARGET: {FOREST_TARGET}"
REQUIRED = {
    'Erdos1016.BoundaryDecay.exceptional_row_le_of_packing',
    'Erdos1016.BoundaryDecay.small_cut_event_bound',
    'Erdos1016.ExceptionalPartners.multigraph_three_links_card_le_cut',
    'Erdos1016.Extremal.LinearExponentialDecay.recurrence_logStar_bound',
    'Erdos1016.FiniteMultiGraph.ConnectedContraction.project_surjective',
    'Erdos1016.FiniteMultiGraph.DisjointRegionCuts.exceptional_partner_card_le',
    'Erdos1016.FiniteMultiGraph.ExteriorComponents.card_le_marked_large_cyclic_blocks',
    'Erdos1016.FiniteMultiGraph.ExteriorComponents.smallCyclicPart_card_le',
    'Erdos1016.FiniteMultiGraph.InducedCycleAvoidance.forest_le_half_add_twenty',
    'Erdos1016.FiniteMultiGraph.InducedSimpleRealization.actual_cycle_links_le',
    'Erdos1016.FiniteMultiGraph.InducedSimpleRealization.cycleSeed_injective',
    'Erdos1016.FiniteMultiGraph.SeedFamilyAvoidance.second_moment_le',
    'Erdos1016.FiniteMultiGraph.average_normalizedSeedIndicator',
    'Erdos1016.FiniteMultiGraph.exists_short_region_packing',
    'Erdos1016.FiniteMultiGraph.isForestWord_iff_no_even_support',
    'Erdos1016.FiniteMultiGraph.loopCycleSpaceEquiv',
    'Erdos1016.FiniteMultiGraph.order_add_two_eq_twice_rank_add_marked_deficit',
    'Erdos1016.FiniteMultiGraph.regionCycleEvent_pair_density',
    'Erdos1016.FiniteMultiGraph.retained_no_loops',
    'Erdos1016.FiniteMultiGraph.retained_simple',
    'Erdos1016.FiniteMultiGraph.smallCut_forest_bound',
    'Erdos1016.LinkCorrelation.multigraph_zeroCut_pair',
    'Erdos1016.Nonbacktracking.DeficitTrace.normalized_even_trace_lower',
    'Erdos1016.PackingCover.mass_le_of_packing',
    'Erdos1016.Problem1016.upper_bound',
    'Erdos1016.Proof.DeficitCutoffParameters.eventually_rank_cycleWordMass_ge',
    'Erdos1016.Proof.ExceptionalLoadCutoffs.eventually_cutoff_exceptional_load_le_quarter',
    'Erdos1016.Proof.ExteriorTreePathCount.card_exterior_trees_le_length_blocks',
    'Erdos1016.Proof.ForestCutoffParameters.eventually_geometry_cutoffs',
    'Erdos1016.Proof.ForestCutoffParameters.link_error_le_envelope',
    'Erdos1016.Proof.LowDegreeTraceCycles.cycleWordMass_ge_log_ratio',
    'Erdos1016.Proof.LowDegreeVertexMass.cycle_mass_at_vertex_le',
    'Erdos1016.Proof.RetainedSizeBounds.eventually_retained_size_and_deficit',
    'Erdos1016.ShortProof.CycleCore.cycleRank_preserved',
    'Erdos1016.ShortProof.CycleCore.networkCycleEquiv',
    'Erdos1016.ShortProof.IncidencePaths.outsideForestProbability_le_region',
    'Erdos1016.ShortProof.actualRankTail_le_of_connected',
    'Erdos1016.ShortProof.coverageDensity_le_outsideForest',
    'Erdos1016.ShortProof.eventually_exists_retained_cycle_supply',
    'Erdos1016.ShortProof.eventually_marked_forest_bound',
    'Erdos1016.ShortProof.exists_budgeted_witness',
    'Erdos1016.ShortProof.exists_marked_subcubic_reduction',
    'Erdos1016.ShortProof.fewComponentForestEstimate',
    'Erdos1016.ShortProof.fewComponentForestEstimate_of_marked_bound',
    'Erdos1016.ShortProof.mainTheorem_of_few_component_forest_estimate',
    'Erdos1016.mainTheorem',
    'Erdos1016.mainTheorem_integer_excess',
}


def axiom_reports(text: str) -> dict[str, list[str]]:
    reports = {}
    for match in re.finditer(r"['‘]([^'’]+)['’]\s+depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        name, axioms = match.groups()
        reports[name] = sorted({a.strip() for a in axioms.split(",") if a.strip()})
    for match in re.finditer(r"['‘]([^'’]+)['’]\s+does not depend on any axioms", text):
        reports[match[1]] = []
    return reports


def check(text: str) -> list[str]:
    problems = []
    if re.search(r"\b(sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|Lean\.ofReduceNat)\b", text):
        problems.append("Admission or compiler-trust axiom in log")
    reports = axiom_reports(text)
    for name in sorted(REQUIRED - reports.keys()):
        problems.append("Missing axiom report: " + name)
    # Check every report occurrence, including duplicate names.
    for match in re.finditer(r"['‘]([^'’]+)['’]\s+depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        name, axioms = match.groups()
        unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
        if unexpected:
            problems.append(f"{name}: unexpected axioms {sorted(unexpected)}")
    for marker in (STATUS, INTEGER_STATUS, FOREST_STATUS):
        if text.splitlines().count(marker) != 1:
            problems.append("Missing or repeated checked statement marker: " + marker)
    if "ENDPOINT_STATUS: CONDITIONAL" in text:
        problems.append("Conditional development evidence cannot verify the final theorem")
    if not re.search(r"\bdef\s+" + re.escape(FOREST_TARGET) + r"\s*:\s*Prop\s*:=", text):
        problems.append("Missing forest-estimate target definition")
    if not re.search(r"\bdef\s+" + re.escape(TARGET) + r"\s*:\s*Prop\s*:=", text):
        problems.append("Missing mathematical target definition")
    if re.search(r"(^|\n).*\berror:", text):
        problems.append("Lean error in audit output")
    return problems


if __name__ == "__main__":
    errors = check(Path(sys.argv[1]).read_text())
    if errors:
        print("\n".join(errors))
        raise SystemExit(1)
    print("Unconditional theorem and forest estimate checked; only standard logical axioms occur.")
