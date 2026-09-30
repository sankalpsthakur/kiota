"""Static checks for the remote Std command; never import/execute its pipeline."""
import ast
from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "std_diagnostic.py"

class StdContainerPolicyTests(unittest.TestCase):
    def setUp(self):
        self.tree = ast.parse(SOURCE.read_text())
        calls = [node for node in ast.walk(self.tree)
                 if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                 and node.func.id == "phase" and node.args
                 and isinstance(node.args[0], ast.Constant)
                 and node.args[0].value == "container-create"]
        self.assertEqual(len(calls), 1)
        self.command = calls[0].args[1]
        self.assertIsInstance(self.command, ast.List)
        self.literals = [node.value if isinstance(node, ast.Constant) else None
                         for node in self.command.elts]

    def test_single_file_local_logs_disable_default_compression(self):
        values = self.literals
        self.assertEqual(values[values.index("--log-driver") + 1], "local")
        options = [values[i + 1] for i, value in enumerate(values) if value == "--log-opt"]
        self.assertEqual(options, ["max-size=1m", "max-file=1", "compress=false"])

    def test_checker_memory_and_no_swap_limits_are_unchanged(self):
        limits = []
        for option in ("--memory", "--memory-swap"):
            node = self.command.elts[self.literals.index(option) + 1]
            self.assertIsInstance(node, ast.Call)
            self.assertIsInstance(node.func, ast.Name)
            self.assertEqual(node.func.id, "str")
            value = ast.literal_eval(node.args[0].left) * ast.literal_eval(node.args[0].right.left) ** ast.literal_eval(node.args[0].right.right)
            limits.append(value)
        self.assertEqual(limits, [6442450944, 6442450944])
        script = self.literals[-1]
        self.assertIn('memory.swap.max)" = 0', script)
        self.assertIn("590s /checker /input", script)

    def test_started_and_verdict_fields_are_explicit(self):
        keys = [key.value for node in ast.walk(self.tree) if isinstance(node, ast.Dict)
                for key in node.keys if isinstance(key, ast.Constant)]
        self.assertIn("checker_started", keys)
        self.assertIn("std_verdict", keys)
        self.assertIn("checker never started:", SOURCE.read_text())


    def test_official_std_metadata_and_immutable_checker_are_pinned(self):
        values = {}
        for node in self.tree.body:
            if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
                try:
                    values[node.targets[0].id] = ast.literal_eval(node.value)
                except (ValueError, TypeError):
                    pass
        self.assertEqual(values["CHECKER"], "c54594965b31ff0fb89bfc311a1ca6e5d017e0cf")
        self.assertEqual(values["INPUT_SHA"], "289ed65a367abdc7388a855d2acf59cc1f401f5e06295acbb8a420682d9f00bd")
        source = SOURCE.read_text()
        self.assertIn("INPUT_BYTES, INPUT_LINES = 596655086, 10826639", source)
        self.assertNotIn("KIOTA_PROGRESS=1", source)
        self.assertIn('"--init"', source)
        self.assertIn('"elan-init"', source)

if __name__ == "__main__":
    unittest.main()
