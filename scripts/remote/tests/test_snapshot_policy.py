"""Read-only AST policy checks; never execute the remote profiler locally."""
import ast
from pathlib import Path
import unittest

class SnapshotPolicyTests(unittest.TestCase):
    def test_reviewed_snapshot_and_resource_gates(self):
        source = (Path(__file__).resolve().parents[1] / "profile_memory.py").read_text()
        tree = ast.parse(source)
        constants = {node.targets[0].id: ast.literal_eval(node.value)
                     for node in tree.body
                     if isinstance(node, ast.Assign) and len(node.targets) == 1
                     and isinstance(node.targets[0], ast.Name)
                     and isinstance(node.value, ast.Constant)}
        self.assertEqual(constants["SMALL_SUITE_SHA256"],
                         "549477be6e17e6fc32b1c744822bfb2580be1faa10bdfc76d5154d18a3c7934e")
        self.assertEqual(constants["EXPECTED_GOOD"], 123)
        self.assertEqual(constants["EXPECTED_TOTAL"], 194)
        self.assertIn('report["archive_sha256"] != SMALL_SUITE_SHA256', source)
        self.assertIn('report["counts"]["good"] != EXPECTED_GOOD', source)
        self.assertIn('len(cases) != EXPECTED_TOTAL', source)
        self.assertIn('"rss_watchdog_mib": 5120', source)
        self.assertIn('"address_space_mib": 8192', source)
        self.assertIn('"per_case_seconds": 120', source)
        self.assertIn('memory_bytes=5120 * 1024 * 1024', source)
        self.assertIn('runner.require_cleanup(result)', source)
