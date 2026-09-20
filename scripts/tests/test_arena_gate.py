import importlib.util
import io
import os
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("arena_gate", Path(__file__).parents[1] / "arena_gate.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class GateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def archive(self, entries):
        path = self.root / "suite.tar.gz"
        with tarfile.open(path, "w:gz") as bundle:
            for name, content in entries:
                payload = content.encode()
                member = tarfile.TarInfo(name)
                member.size = len(payload)
                bundle.addfile(member, io.BytesIO(payload))
        return path

    def binary(self, body):
        path = self.root / "checker"
        path.write_text("#!/usr/bin/env python3\n" + body)
        path.chmod(0o755)
        return path

    def run_gate(self, body, entries=None, timeout=2):
        binary = self.binary(body)
        archive = self.archive(entries or [("good/a.ndjson", "0"), ("bad/b.ndjson", "1")])
        return gate.run_gate(binary, archive, self.root / "report", ["default", "nbe"], timeout, 1, 1)

    def test_exact_verdicts_and_modes(self):
        report = self.run_gate("import sys\nfrom pathlib import Path\nsys.exit(int(Path(sys.argv[1]).read_text()))\n")
        self.assertTrue(report["passed"])
        self.assertEqual(len(report["results"]), 4)
        self.assertFalse(report["full_corpus_verified"])
        self.assertEqual(len(report["archive_sha256"]), 64)

    def test_decline_is_not_rejection(self):
        report = self.run_gate("raise SystemExit(2)\n")
        self.assertFalse(report["passed"])
        self.assertTrue(all(r["outcome"] == "decline" for r in report["results"]))

    def test_always_accept_is_unsound(self):
        report = self.run_gate("raise SystemExit(0)\n")
        self.assertFalse(report["passed"])
        self.assertEqual(sum(not r["passed"] for r in report["results"]), 2)

    def test_crash_is_not_rejection(self):
        report = self.run_gate("import os, signal\nos.kill(os.getpid(), signal.SIGKILL)\n")
        self.assertFalse(report["passed"])
        self.assertTrue(all(r["outcome"] == "crash" for r in report["results"]))

    def test_timeout_is_failure(self):
        report = self.run_gate("import time\ntime.sleep(10)\n", timeout=0.05)
        self.assertFalse(report["passed"])
        self.assertTrue(all(r["outcome"] == "timeout" for r in report["results"]))

    def test_inherited_skip_flags_removed(self):
        with patch.dict(os.environ, {"KIOTA_MAX_DECL": "1", "KIOTA_SKIP_DECLS": "1,2", "KIOTA_NBE": "yes"}):
            report = self.run_gate("import os,sys\nfrom pathlib import Path\nassert 'KIOTA_MAX_DECL' not in os.environ\nassert 'KIOTA_SKIP_DECLS' not in os.environ\nassert os.environ.get('KIOTA_NBE') in (None, '1')\nsys.exit(int(Path(sys.argv[1]).read_text()))\n")
        self.assertTrue(report["passed"])
        self.assertIn("KIOTA_MAX_DECL", report["removed_environment_variables"])

    def test_incomplete_suite_fails(self):
        report = self.run_gate("raise SystemExit(0)\n", [("good/a.ndjson", "0")])
        self.assertFalse(report["passed"])
        self.assertIn("incomplete suite", report["error"])

    def test_path_traversal_fails(self):
        report = self.run_gate("raise SystemExit(0)\n", [("../escape", "0")])
        self.assertFalse(report["passed"])
        self.assertIn("unsafe archive path", report["error"])
        self.assertFalse((self.root / "escape").exists())

    def test_duplicate_member_fails(self):
        report = self.run_gate("raise SystemExit(0)\n", [("good/a", "0"), ("good/a", "1")])
        self.assertFalse(report["passed"])
        self.assertIn("duplicate test", report["error"])

    def test_unknown_exit_is_crash(self):
        self.assertEqual(gate.classify(137, False), "crash")
        self.assertEqual(gate.classify(3, False), "error")
        self.assertEqual(gate.classify(124, True), "timeout")


if __name__ == "__main__":
    unittest.main()
