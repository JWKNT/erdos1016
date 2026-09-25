#!/usr/bin/env python3
"""Regression checks for audit scope and admission/import detection, not Lean proofs."""
from pathlib import Path
import tempfile
import unittest

from project_inventory import inventory


class InventoryChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "Erdos1016").mkdir()
        self.write("Erdos1016", "import Erdos1016.Good\n")
        self.write("Erdos1016.Good", "theorem good : True := by trivial\n")

    def write(self, module, source):
        path = self.root.joinpath(*module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

    def test_comments_strings_and_historical_sources_are_excluded(self):
        self.write("Erdos1016.Good", '''/- sorry /- axiom nested -/ import Erdos1016.Missing -/
-- import Erdos1016.Missing
def message := "sorry admit axiom"
theorem good : True := by trivial
''')
        self.write("history.Bad", "axiom not_part_of_library : False\n")
        result = inventory(self.root)
        self.assertTrue(result["all_sources_structural_checks_passed"])
        self.assertEqual(result["counts"]["all_library_sources"]["modules"], 2)

    def test_unimported_broken_experiment_is_reported_separately(self):
        self.write("Erdos1016.Experiment", "import Erdos1016.Missing\n")
        result = inventory(self.root)
        self.assertTrue(result["umbrella_structural_checks_passed"])
        self.assertFalse(result["all_sources_structural_checks_passed"])
        self.assertEqual(result["outside_umbrella_modules"], ["Erdos1016.Experiment"])
        self.assertEqual(result["errors"][0]["module"], "Erdos1016.Experiment")

    def test_imported_admission_fails_active_audit(self):
        self.write("Erdos1016.Good", "theorem missing : False := by sorry\n")
        result = inventory(self.root)
        self.assertFalse(result["umbrella_structural_checks_passed"])
        self.assertEqual(result["source_risk_tokens"], [
            {"module": "Erdos1016.Good", "line": 1, "token": "sorry"}])

    def test_import_cycle_fails_and_closure_terminates(self):
        self.write("Erdos1016.Good", "import Erdos1016\n")
        result = inventory(self.root)
        self.assertFalse(result["umbrella_structural_checks_passed"])
        self.assertIn("import cycle", result["errors"][0]["message"])

    def test_duplicate_import_is_advisory_and_fingerprint_tracks_changes(self):
        before = inventory(self.root)
        self.write("Erdos1016", "import Erdos1016.Good\nimport Erdos1016.Good\n")
        after = inventory(self.root)
        self.assertTrue(after["all_sources_structural_checks_passed"])
        self.assertEqual(after["duplicate_imports"][0]["count"], 2)
        self.assertNotEqual(before["source_set_sha256"], after["source_set_sha256"])


if __name__ == "__main__":
    unittest.main()
