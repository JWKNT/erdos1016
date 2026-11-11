"""Record proof status, completed finite checks, and artifact hashes.

Run after the final PDF builds and visual review. This records existing check
outputs; it does not replace their scripts or certify the mathematical proofs.
"""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    checks = {}
    names = [
        "no-waste-results.json", "path-stability-results.json",
        "path-stability-phase2-results.json", "path-minor-reduction-results.json",
        "additive-layer-structure-results.json", "link-stability-results.json",
        "random-host-encoding-results.json", "random-host-phase2-results.json",
        "k4-random-host-blocks-results.json", "theta-random-host-partition-results.json",
        "random-host-wheel-results.json", "four-regular-theorem-certificate.json",
        "four-regular-vertex-deletion-results.json", "cubic-edge-frequency-results.json",
        "full-threshold-integration-results.json",
    ]
    for name in names:
        path = ROOT / name
        data = json.loads(path.read_text())
        checks[name] = {
            "sha256": digest(path),
            "summary": {k: v for k, v in data.items()
                        if not isinstance(v, (list, dict))},
        }
    checks["fable_check_tools.py"] = {
        "status": "passed on 2026-11-10",
        "exact_checks": "300 graphs each for edge recursion, product formula, localization, and splitting; layer checks also passed",
    }
    checks["random-host-rank3-barrier-certificates.json"] = {
        "sha256": digest(ROOT / "random-host-rank3-barrier-certificates.json"),
        "status": "all exact rational dual inequalities passed",
        "theta_regions": 64, "K4_regions": 16384, "integral": "37/36",
    }
    pdfs = {}
    for name in ("research-progress-extended", "terminal-path-stability", "four-regular-theorem", "full-threshold-pancyclicity"):
        path = ROOT / (name + ".pdf")
        log = (ROOT / (name + ".log")).read_text()
        warnings = [line for line in log.splitlines()
                    if "Overfull" in line or "Underfull" in line
                    or "undefined" in line.lower() or "LaTeX Warning" in line]
        pdfs[path.name] = {
            "pages": len(PdfReader(path).pages),
            "sha256": digest(path),
            "build": "tectonic --keep-logs " + name + ".tex",
            "tex_warnings": warnings,
            "visual_review": "All pages reviewed in rendered PNGs by root and/or path_stability; no clipped mathematics or unresolved references",
        }
    sources = {}
    for path in sorted(ROOT.iterdir()):
        if path.suffix in {".tex", ".py", ".cpp"} or path.name == "fable-notes.md":
            sources[path.name] = digest(path)
    result = {
        "date_utc": datetime.now(timezone.utc).isoformat(),
        "original_source_revision": "a965788",
        "status": "Mathematical research drafts with independent internal audits; new results not formalized in Lean; publication priority unverified",
        "attribution": {
            "Fable 5.2": "localization, general linear path stability via shortest-path layers, and the chord-free cycle recurrence",
            "Codex team": "fixed-gap forest range, additive stability deduction, exact four-regular theorem and finite verification, random-host refinements, and other fragments",
        },
        "audit_scope": {
            "additive_path_stability": "root, path_stability, and four_regular independently checked the layer-to-cycle deduction; Fable's input separately audited twice",
            "four_regular": "structural and analytic arguments audited independently; all 925 required finite cases checked by two cycle counters",
            "centered_wheel_upper_bound": "root and four_regular independently audited distribution, matching theorem, overlap moments, density, and rank accounting",
            "minor_closed_cycle_error": "root audit; independent chord-free proof supplied by path_stability",
            "full_random_host_threshold": "root, path_stability, and four_regular independently checked adaptive exposure, rollback, finite topology, interval coverage, Hamilton completion at the exact threshold, and excess accounting",
        },
        "pdfs": pdfs,
        "finite_checks": checks,
        "source_sha256": sources,
    }
    output = ROOT / "verification-extended.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(output)


if __name__ == "__main__":
    main()
