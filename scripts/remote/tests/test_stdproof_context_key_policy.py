"""Static checks for the remote StdProof command; never import/execute its pipeline."""
import ast
from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "stdproof_context_key_diagnostic.py"

class StdProofContextKeyContainerPolicyTests(unittest.TestCase):
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
        self.assertIn("120s /checker /input", script)

    def test_started_and_verdict_fields_are_explicit(self):
        keys = [key.value for node in ast.walk(self.tree) if isinstance(node, ast.Dict)
                for key in node.keys if isinstance(key, ast.Constant)]
        self.assertIn("checker_started", keys)
        self.assertIn("stdproof_verdict", keys)
        self.assertIn("checker never started:", SOURCE.read_text())


    def test_selected_std_is_never_full_std_proof(self):
        source = SOURCE.read_text()
        self.assertIn('CHECKER = "258a309f94afe506cf0c866c6551fb61ff625be3"', source)
        self.assertIn('TARGET = "Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq._unary"', source)
        self.assertIn('"full_std_verified": False', source)
        self.assertIn('"full_corpus_verified": False', source)
        self.assertIn('"arena_rank_verified": False', source)
        self.assertIn('target Std theorem absent', source)
        self.assertNotIn('MATHLIB', source)
        self.assertIn('"--init"', source)
        self.assertIn('"elan-init"', source)

    def test_replay_requires_frozen_target_input_before_checker_fetch(self):
        source = SOURCE.read_text()
        self.assertIn('INPUT_SHA = "b13db37bcbae93d41d7d20405050beade15689511f1bb689ad866435270c33e6"', source)
        self.assertIn("INPUT_BYTES, INPUT_LINES, INPUT_DECLARATIONS = 22877330, 436979, 4066", source)
        for guard in ("actual_sha != INPUT_SHA", "source.stat().st_size != INPUT_BYTES", "lines != INPUT_LINES", "len(declared) != INPUT_DECLARATIONS"):
            self.assertIn(guard, source)
        self.assertLess(source.index("selected Std input differs from frozen baseline"), source.index('fetch("checker",'))

    def test_context_key_mode_is_explicit_and_opt_in(self):
        source = SOURCE.read_text()
        self.assertIn('MODE not in ("lazy-head", "ctx-key-memo")', source)
        self.assertIn('*(["--env", "KIOTA_CTX_KEY_MEMO=1"] if MODE == "ctx-key-memo" else [])', source)
        self.assertIn('"context_key_memo_enabled": MODE == "ctx-key-memo"', source)
        self.assertIn('"stdproof-context-key-report" / MODE', source)

if __name__ == "__main__":
    unittest.main()
