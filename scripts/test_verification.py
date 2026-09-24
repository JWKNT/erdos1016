"""The verification gate must reject incomplete or misleading evidence."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

from check_axiom_log import ALLOWED, REQUIRED, STATUS, TARGET, check
from verify import fingerprint, structural_errors


class AxiomAuditTests(unittest.TestCase):
    def valid_log(self):
        return f'def {TARGET} : Prop := True\n{STATUS}\n' + '\n'.join(
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
        for axiom in ['sorryAx', 'Lean.ofReduceBool', 'UnprovedInput']:
            with self.subTest(axiom=axiom):
                self.assertTrue(check(self.valid_log() + f"\n'Erdos1016.mainTheorem' depends on axioms: [{axiom}]"))

    def test_statement_marker_and_definition_are_required(self):
        self.assertTrue(check(self.valid_log().replace(STATUS, '')))
        self.assertTrue(check(self.valid_log().replace(f'def {TARGET}', 'theorem other')))
        self.assertTrue(check(self.valid_log() + '\naudit.lean:1:0: error: mismatch'))


class VerificationTests(unittest.TestCase):
    def report(self):
        return {'all_sources_structural_checks_passed': True, 'outside_umbrella_modules': [],
                'duplicate_imports': [], 'identical_source_groups': [], 'modules': {'Erdos1016.Main': {}}}

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

    def test_fingerprint_includes_audits_pins_and_tools(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ['Erdos1016.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
                         'audits/MainTheoremAudit.lean', 'scripts/verify.py', '.github/workflows/verify.yml']:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('initial')
            before = fingerprint(root)
            for name in ['audits/MainTheoremAudit.lean', 'lean-toolchain', 'scripts/verify.py']:
                path = root / name
                path.write_text('changed')
                self.assertNotEqual(before, fingerprint(root))
                path.write_text('initial')
            (root / '.verification').mkdir()
            (root / '.verification/result.json').write_text('generated')
            self.assertEqual(before, fingerprint(root))


if __name__ == '__main__':
    unittest.main()
