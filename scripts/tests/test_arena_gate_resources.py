import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("arena_gate_resources", Path(__file__).parents[1] / "arena_gate.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class ResourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.binary = self.root / "checker"
        self.binary.write_text("#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\nsys.exit(int(Path(sys.argv[1]).read_text()))\n")
        self.binary.chmod(0o755)
        self.archive = self.root / "suite.tar.gz"
        with tarfile.open(self.archive, "w:gz") as bundle:
            for name, payload in [("good/a.ndjson", b"0"), ("bad/b.ndjson", b"1")]:
                member = tarfile.TarInfo(name)
                member.size = len(payload)
                bundle.addfile(member, io.BytesIO(payload))
        self.output = self.root / "report"

    def run_gate(self, **kwargs):
        return gate.run_gate(self.binary, self.archive, self.output,
                             ["default"], 2, 1, 1, **kwargs)

    def test_child_receives_resource_limits(self):
        self.binary.write_text("#!/usr/bin/env python3\nimport resource,sys\nfrom pathlib import Path\nassert resource.getrlimit(resource.RLIMIT_AS) == (256 * 1024**2,) * 2\nassert resource.getrlimit(resource.RLIMIT_CORE) == (0, 0)\nassert resource.getrlimit(resource.RLIMIT_FSIZE) == (64 * 1024**2,) * 2\nsys.exit(int(Path(sys.argv[1]).read_text()))\n")
        report = self.run_gate(memory_mib=256)
        self.assertTrue(report["passed"])
        self.assertTrue(report["complete"])
        self.assertEqual(report["address_space_limit_mib"], 256)

    def test_checkpoint_written_before_each_case(self):
        original = gate.run_case
        calls = []

        def inspect(binary, case, mode, *args):
            saved = json.loads((self.output / "report.json").read_text())
            self.assertFalse(saved["passed"])
            self.assertFalse(saved["complete"])
            self.assertEqual(saved["running"], {"mode": mode, "test": case[0]})
            self.assertEqual(len(saved["results"]), len(calls))
            calls.append(case[0])
            return original(binary, case, mode, *args)

        with patch.object(gate, "run_case", side_effect=inspect):
            report = self.run_gate()
        self.assertEqual(len(calls), 2)
        self.assertIsNone(report["running"])
        self.assertEqual(json.loads((self.output / "report.json").read_text()), report)

    def test_interrupted_run_cannot_claim_pass(self):
        with patch.object(gate, "run_case", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.run_gate()
        saved = json.loads((self.output / "report.json").read_text())
        self.assertFalse(saved["complete"])
        self.assertFalse(saved["passed"])
        self.assertIsNotNone(saved["running"])

    def test_failed_exec_is_error_not_reject(self):
        proc = subprocess.run([sys.executable, str(Path(gate.__file__).resolve()),
                               "--exec-limited", "256", str(self.root / "missing"), "input"],
                              capture_output=True, text=True, timeout=2)
        self.assertEqual(proc.returncode, 3)
        self.assertIn("child setup failed", proc.stderr)

    def test_failures_retain_diagnostic_tail(self):
        self.binary.write_text("#!/usr/bin/env python3\nimport sys\nprint('regression diagnostic', file=sys.stderr)\nraise SystemExit(2)\n")
        report = self.run_gate()
        self.assertFalse(report["passed"])
        self.assertTrue(report["complete"])
        self.assertTrue(all("regression diagnostic" in r["diagnostic_tail"] for r in report["results"]))

    def test_invalid_resource_limit_is_rejected(self):
        with self.assertRaises(ValueError):
            self.run_gate(memory_mib=0)


if __name__ == "__main__":
    unittest.main()
