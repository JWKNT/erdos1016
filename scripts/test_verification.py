"""The verification gate must reject incomplete or misleading evidence."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

from check_axiom_log import ALLOWED, FOREST_TARGET, FOREST_STATUS, INTEGER_STATUS, REQUIRED, STATUS, TARGET, check
from verify import REQUIRED_CHECKS, fingerprint, initial_status, record_completion, structural_errors


class AxiomAuditTests(unittest.TestCase):
    def valid_log(self):
        return f'def {TARGET} : Prop := True\ndef {FOREST_TARGET} : Prop := True\n{STATUS}\n{INTEGER_STATUS}\n{FOREST_STATUS}\n' + '\n'.join(
            f"'{name}' depends on axioms: [{', '.join(sorted(ALLOWED))}]" for name in sorted(REQUIRED))

    def test_complete_log(self):
        self.assertEqual(check(self.valid_log()), [])

    def test_every_report_is_required(self):
        text = self.valid_log()
        for name in REQUIRED:
            with self.subTest(name=name):
                self.assertTrue(check('\n'.join(line for line in text.splitlines()
                                                 if not line.startswith(f"'{name}'"))))

    def test_extra_axioms_and_duplicate_reports_fail(self):
        for axiom in ['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler', 'Lean.ofReduceNat', 'UnprovedInput']:
            with self.subTest(axiom=axiom):
                self.assertTrue(check(self.valid_log() + f"\n'Erdos1016.mainTheorem' depends on axioms: [{axiom}]"))

    def test_statement_marker_and_definition_are_required(self):
        self.assertTrue(check(self.valid_log().replace(STATUS, '')))
        self.assertTrue(check(self.valid_log().replace(f'def {TARGET}', 'theorem other')))
        self.assertTrue(check(self.valid_log() + '\naudit.lean:1:0: error: mismatch'))

    def test_conditional_old_logs_and_missing_new_roots_are_rejected(self):
        conditional = self.valid_log().replace(STATUS,
            f'ENDPOINT_STATUS: CONDITIONAL; INPUT: {FOREST_TARGET}; TARGET: {TARGET}')
        self.assertTrue(check(conditional))
        self.assertTrue(check(self.valid_log() + '\n' + conditional))
        for marker in [STATUS, INTEGER_STATUS, FOREST_STATUS]:
            with self.subTest(marker=marker):
                self.assertTrue(check(self.valid_log().replace(marker, '')))
                self.assertTrue(check(self.valid_log() + '\n' + marker))
        self.assertTrue(check(self.valid_log().replace(f'def {FOREST_TARGET}', 'def OtherInput')))

    def test_nonstandard_axiom_cannot_be_hidden_by_later_clean_report(self):
        name = 'Erdos1016.mainTheorem'
        dirty = f"'{name}' depends on axioms: [UnprovedInput]\n"
        self.assertTrue(check(dirty + self.valid_log()))

    def test_archived_unconditional_roots_do_not_suffice(self):
        # The old proof's main name and marker cannot replace the shorter
        # proof's explicit unconditional forest estimate and retained graph.
        lines = [line for line in self.valid_log().splitlines()
                 if not line.startswith("'Erdos1016.ShortProof.fewComponentForestEstimate'")]
        self.assertTrue(check('\n'.join(lines)))

    def test_required_profile_matches_lean_audit(self):
        import re
        audit = (Path(__file__).resolve().parents[1] / 'audits/TheoremAudit.lean').read_text()
        self.assertEqual(set(re.findall(r'^#print axioms (\S+)$', audit, re.M)), REQUIRED)


class VerificationTests(unittest.TestCase):
    def report(self):
        return {'all_sources_structural_checks_passed': True, 'outside_umbrella_modules': [],
                'duplicate_imports': [], 'identical_source_groups': [], 'modules': {'Erdos1016': {}}}

    def test_orphans_duplicates_and_legacy_names_fail(self):
        valid = self.report()
        self.assertEqual(structural_errors(valid), [])
        for field in ['outside_umbrella_modules', 'duplicate_imports', 'identical_source_groups']:
            report = deepcopy(valid)
            report[field] = ['unexpected']
            self.assertTrue(structural_errors(report))
        for name in ['Erdos1016.Paper.X', 'Erdos1016.SectionTenX', 'Erdos1016.X20260924']:
            report = deepcopy(valid)
            report['modules'][name] = {}
            self.assertTrue(structural_errors(report))

    def test_running_report_does_not_claim_completion(self):
        report = initial_status()
        self.assertEqual(report['status'], 'running')
        self.assertEqual(report['formalization_status'], 'unverified')
        self.assertFalse(report['unconditional_main_theorem_proved'])
        self.assertIsNone(report['remaining_mathematical_premises'])

    def test_only_all_successful_checks_can_claim_completion(self):
        report = {**initial_status(), 'checks': sorted(REQUIRED_CHECKS)}
        self.assertEqual(record_completion(report, [], True), 0)
        self.assertEqual(report['formalization_status'], 'complete')
        self.assertTrue(report['unconditional_main_theorem_proved'])
        self.assertEqual(report['remaining_mathematical_premises'], [])
        for missing in REQUIRED_CHECKS - {'verification_inputs_unchanged'}:
            with self.subTest(missing=missing):
                report = {**initial_status(), 'checks': sorted(REQUIRED_CHECKS - {missing})}
                self.assertEqual(record_completion(report, [], True), 1)
                self.assertFalse(report['unconditional_main_theorem_proved'])
                self.assertEqual(report['formalization_status'], 'unverified')

    def test_failure_and_changed_inputs_revoke_any_completion_claim(self):
        for errors, unchanged in [(['Lean failed'], True), ([], False)]:
            report = {**initial_status(), 'checks': sorted(REQUIRED_CHECKS),
                      'formalization_status': 'complete', 'unconditional_main_theorem_proved': True}
            self.assertEqual(record_completion(report, errors, unchanged), 1)
            self.assertEqual(report['status'], 'failed')
            self.assertFalse(report['unconditional_main_theorem_proved'])
            self.assertIsNone(report['remaining_mathematical_premises'])

    def test_fingerprint_includes_audits_pins_and_tools(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ['Erdos1016.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
                         'audits/TheoremAudit.lean', 'scripts/verify.py', '.github/workflows/verify.yml']:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('initial')
            before = fingerprint(root)
            for name in ['audits/TheoremAudit.lean', 'lean-toolchain', 'scripts/verify.py']:
                path = root / name
                path.write_text('changed')
                self.assertNotEqual(before, fingerprint(root))
                path.write_text('initial')
            (root / '.verification').mkdir()
            (root / '.verification/result.json').write_text('generated')
            self.assertEqual(before, fingerprint(root))
            (root / 'old').mkdir()
            (root / 'old' / 'Main.lean').write_text('archived source')
            self.assertEqual(before, fingerprint(root))


if __name__ == '__main__':
    unittest.main()
