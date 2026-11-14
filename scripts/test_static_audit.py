"""Regression tests for the package's source-integrity gate (NOT Lean proof tests)."""
from pathlib import Path
import importlib.util
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class StaticAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.path = Path(self.temp.name) / 'candidate'
        shutil.copytree(ROOT, self.path,
                        ignore=shutil.ignore_patterns('.local-replay','.lake','__pycache__'))
        # Import exactly the copied auditor, so its ROOT points to the copy.
        spec = importlib.util.spec_from_file_location('candidate_static_audit',
                            self.path / 'scripts/static_audit.py')
        self.audit_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.audit_module)

    def tearDown(self):
        self.temp.cleanup()

    def test_unmodified_snapshot_passes(self):
        self.assertEqual(self.audit_module.audit()['status'], 'PASS_STATIC_ONLY')

    def test_challenge_validator_rejects_plain_import(self):
        verifier=(self.path/'scripts/verify_challenge.py').read_text()
        challenge=self.path/'challenge/Challenge.lean'
        source=challenge.read_text()
        challenge.write_text(source.replace(
            'public import RML.Fourier.Vaaler.Discrepancy.TorusBox',
            'import RML.Fourier.Vaaler.Discrepancy.TorusBox',1))
        import subprocess
        proc=subprocess.run(['python3','scripts/verify_challenge.py'],cwd=self.path,
            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        self.assertNotEqual(proc.returncode,0)
        self.assertIn('noncanonical import',proc.stdout)
        self.assertIn('^public import',verifier)

    def test_missing_module_header_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        text = p.read_text()
        self.assertTrue(text.startswith('module\n\n'))
        p.write_text(text.replace('module\n\n', '', 1))
        findings = self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('module wrapper invalid' in item for item in findings['problems']))

    def test_nonpublic_import_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        text = p.read_text()
        self.assertIn('public import ', text)
        p.write_text(text.replace('public import ', 'import ', 1))
        findings = self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('module wrapper invalid' in item for item in findings['problems']))

    def test_source_modification_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        p.write_text(p.read_text()+'\n-- accidental modification\n')
        findings=self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('proof source was edited' in p for p in findings['problems']))

    def test_bialer_notice_tampering_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Internal/Analytic/FejerTriangle.lean'
        p.write_text(p.read_text().replace(
            'MODIFIED for VAALER toolkit, 2026-11-12',
            'MODIFIED for VAALER toolkit, 2026-11-13'))
        findings = self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('notice' in p for p in findings['problems']))

    def test_bialer_other_source_edit_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Internal/Analytic/SincSquare.lean'
        p.write_text(p.read_text() + '\n-- unauthorized source edit\n')
        findings = self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('proof source was edited' in p for p in findings['problems']))

    def test_unresolved_local_import_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        p.write_text('import RML.Fourier.DoesNotExist\n'+p.read_text())
        findings=self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('unresolved local import' in p for p in findings['problems']))

    def test_legacy_import_is_detected(self):
        p = self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        p.write_text('import PaperB.DoNotShip\n'+p.read_text())
        findings=self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('forbidden legacy import' in p for p in findings['problems']))

    def test_admission_is_detected(self):
        p=self.path / 'RML/Fourier/Vaaler/Pointwise.lean'
        p.write_text(p.read_text()+'\ntheorem bad : True := by sorry\n')
        findings=self.audit_module.audit()
        self.assertEqual(findings['status'], 'FAIL_STATIC')
        self.assertTrue(any('admission' in p for p in findings['problems']))


if __name__ == '__main__':
    unittest.main()
