#!/usr/bin/env python3
"""Inventory Lean sources and imports. Kernel checking is performed separately."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys

def code_only(text: str) -> str:
    """Remove nested Lean block comments, line comments and strings.
    Newlines and offsets are retained. Not a complete Lean syntax parser.
    """
    out = list(text)
    i = depth = 0
    quote = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif quote:
            if text[i] == '\\':
                out[i] = ' '; i += 1
                if i < len(text):
                    if text[i] != '\n': out[i] = ' '
                    i += 1
            elif text[i] == '"':
                out[i] = ' '; quote = False; i += 1
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out[i:j] = ' ' * (j-i); i = j
        elif text[i] == '"':
            out[i] = ' '; quote = True; i += 1
        else:
            i += 1
    if depth or quote:
        raise ValueError('unclosed block comment or string')
    return ''.join(out)


ROOT = Path(__file__).resolve().parents[1]
DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom)\s+",
    re.M,
)
RISK_TOKEN = re.compile(r"\b(?:sorry|admit|axiom|sorryAx|native_decide|unsafe)\b")


def source_paths(root: Path) -> dict[str, Path]:
    paths = [root / "Erdos1016.lean", *sorted((root / "Erdos1016").rglob("*.lean"))]
    return {".".join(p.relative_to(root).with_suffix("").parts): p for p in paths}


def closure(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    pending = [start]
    while pending:
        name = pending.pop()
        if name in seen or name not in graph:
            continue
        seen.add(name)
        pending.extend(graph[name])
    return seen


def inventory(root: Path) -> dict:
    paths = source_paths(root)
    records: dict[str, dict] = {}
    graph: dict[str, list[str]] = {}
    errors: list[dict] = []
    duplicate_imports: list[dict] = []
    token_findings: list[dict] = []
    content_groups: dict[str, list[str]] = defaultdict(list)
    for name, path in paths.items():
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        try:
            code = code_only(text)
        except ValueError as exc:
            errors.append({"module": name, "message": str(exc)})
            code = ""
        imports = [item for match in re.finditer(r"^\s*import\s+([^\n]+)", code, re.M)
                   for item in match[1].split()]
        graph[name] = [item for item in imports if item == "Erdos1016"
                       or item.startswith("Erdos1016.")]
        for item in graph[name]:
            if item not in paths:
                errors.append({"module": name, "message": f"missing local import {item}"})
        for item, count in Counter(imports).items():
            if count > 1:
                duplicate_imports.append({"module": name, "import": item, "count": count})
        for match in RISK_TOKEN.finditer(code):
            token_findings.append({"module": name, "line": code.count("\n", 0, match.start()) + 1,
                                   "token": match[0]})
        digest = hashlib.sha256(raw).hexdigest()
        content_groups[digest].append(name)
        records[name] = {
            "path": path.relative_to(root).as_posix(), "sha256": digest,
            "lines": len(text.splitlines()),
            "nonblank_code_lines": sum(bool(line.strip()) for line in code.splitlines()),
            "declaration_counts_lexical": dict(Counter(DECLARATION.findall(code))),
            "imports": imports,
            "scratch_or_attempt_name": bool(re.search(r"Scratch|Attempt", name)),
        }
    # Check all files, including experimental files outside the umbrella closure.
    state: dict[str, int] = {}
    order: list[str] = []
    def visit(name: str, chain: list[str]) -> None:
        if name not in graph or state.get(name) == 2:
            return
        if state.get(name) == 1:
            errors.append({"module": name, "message": "import cycle: " + " -> ".join(chain + [name])})
            return
        state[name] = 1
        for dependency in graph[name]:
            visit(dependency, chain + [name])
        state[name] = 2
        order.append(name)
    for name in graph:
        visit(name, [])
    reached = closure(graph, "Erdos1016")
    active_errors = [item for item in errors if item["module"] in reached]
    active_tokens = [item for item in token_findings if item["module"] in reached]
    unreached = sorted(set(records) - reached)
    scratch = {name for name, record in records.items() if record["scratch_or_attempt_name"]}
    def counts(names: set[str] | list[str]) -> dict:
        return {"modules": len(names), "lines": sum(records[name]["lines"] for name in names)}
    areas: dict[str, set[str]] = defaultdict(set)
    declarations: Counter = Counter()
    for name, record in records.items():
        record["in_umbrella_closure"] = name in reached
        areas[name.split(".")[1] if "." in name else "(umbrella)"].add(name)
        declarations.update(record["declaration_counts_lexical"])
    # Fingerprint the exact source set this report describes, independent of mtimes.
    manifest = "".join(f"{name} {records[name]['sha256']}\n" for name in sorted(records))
    return {
        "kind": "Static source inventory, not Lean elaboration or proof completeness",
        "source_set_sha256": hashlib.sha256(manifest.encode()).hexdigest(),
        "umbrella_structural_checks_passed": not active_errors and not active_tokens,
        "all_sources_structural_checks_passed": not errors and not token_findings,
        "umbrella_errors": active_errors,
        "errors": errors, "source_risk_tokens": token_findings,
        "counts": {"all_library_sources": counts(set(records)),
                   "umbrella_closure": counts(reached), "outside_umbrella": counts(unreached),
                   "scratch_or_attempt_names": counts(scratch),
                   "imported_scratch_or_attempt_names": counts(scratch & reached)},
        "by_area": {area: {"all": counts(names), "umbrella": counts(names & reached)}
                    for area, names in sorted(areas.items())},
        "declaration_counts_lexical_not_proof_coverage": dict(declarations),
        "duplicate_imports": duplicate_imports,
        "identical_source_groups": [names for names in content_groups.values() if len(names) > 1],
        "outside_umbrella_modules": unreached,
        "all_modules_topological_order": order,
        "modules": records,
        "limitations": [
            "Imports and declarations are scanned lexically after comments and strings are removed.",
            "Import closure over-approximates theorem dependencies; it is not an axiom audit.",
            "No source-risk tokens does not prove kernel checking or discharge theorem hypotheses.",
            "Unimported modules may contain useful proofs; Scratch/Attempt names do not imply failure.",
            "Line and declaration counts are not estimates of mathematical proof coverage.",
        ],
    }


def main() -> int:
    report = inventory(ROOT)
    destination = ROOT / ".verification/inventory.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("all_sources_structural_checks_passed", "counts", "errors",
                       "source_risk_tokens", "outside_umbrella_modules", "source_set_sha256")}, indent=2))
    return 0 if report["all_sources_structural_checks_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
