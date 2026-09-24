#!/usr/bin/env python3
"""Validate the statement marker and the complete set of kernel axiom reports."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGET = "Erdos1016.Problem1016.MainTheorem"
STATUS = f"ENDPOINT_STATUS: UNCONDITIONAL; TARGET: {TARGET}"
REQUIRED = {
        'Erdos1016.mainTheorem',
        'Erdos1016.mainTheorem_integer_excess',
        'Erdos1016.Proof.UniformCoreDecayProof.exists_uniform_core_decay',
        'Erdos1016.Proof.SelectedConditionalLoad.eventually_selected_conditional_load',
        'Erdos1016.Proof.RetainedCycleAvoidance.finite_avoidance_le',
        'Erdos1016.Proof.ResidualCoreCycleLoad.vertexLoad_le',
        'Erdos1016.Proof.CleanupConstruction.exists_cleanup_output',
        'Erdos1016.Proof.UniformDecayReduction.forestProbabilityBound',
        'Erdos1016.Problem1016.upper_bound',
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
    if STATUS not in text:
        problems.append("Missing checked unconditional theorem signature")
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
    print("Unconditional theorem checked; only standard logical axioms occur.")
