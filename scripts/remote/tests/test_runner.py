"""Lightweight fake-binary tests. Scratch artifacts are intentionally retained."""
from contextlib import redirect_stdout
from copy import deepcopy
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

REMOTE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("remote_runner", REMOTE / "runner.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

HEADER = {"lean": {"version": "test-lean", "githash": "test-source"},
          "exporter": {"name": "fake-exporter", "version": "test-exporter"},
          "format": {"version": "test-format"}}
FAKE = '''import json, os, signal, subprocess, sys, time
json.loads(sys.stdin.readline())
case = json.loads(sys.stdin.read())
print(json.dumps({k:v for k,v in os.environ.items() if k.startswith("KIOTA_")}), flush=True)
if case.get("marker"):
    open(case["marker"], "x").close()
if case.get("child"):
    code = "import signal,time,pathlib; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(5); pathlib.Path(" + repr(case["child"]) + ").touch()"
    child = subprocess.Popen([sys.executable, "-c", code])
    with open(case["pidfile"], "x") as f: f.write(str(child.pid))
if case.get("flood"):
    while True:
        print("x" * 8192, flush=True)
        time.sleep(.005)
if case.get("mutate"):
    with open(case["mutate"], "ab") as f: f.write(b" ")
time.sleep(case.get("sleep", 0))
if case.get("signal"):
    os.kill(os.getpid(), signal.SIGTERM)
sys.exit(case.get("code", 0))
'''


class RunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo = Path(tempfile.mkdtemp(prefix="kiota-fake-repo-")).resolve()
        env = runner.clean_environment("default")
        subprocess.run(["git", "init", "-q", str(cls.repo)], check=True, env=env)
        # Tiny synthetic Git objects: no commits or changes in the user's repo.
        tree = subprocess.check_output(["git", "-C", str(cls.repo), "hash-object", "-t", "tree",
                                        "-w", "--stdin"], input=b"", env=env).decode().strip()
        commit = (f"tree {tree}\nauthor Fixture <fixture@example.invalid> 1 +0000\n"
                  "committer Fixture <fixture@example.invalid> 1 +0000\n\nfixture\n").encode()
        cls.sha = subprocess.check_output(["git", "-C", str(cls.repo), "hash-object", "-t", "commit",
                                           "-w", "--stdin"], input=commit, env=env).decode().strip()
        subprocess.run(["git", "-C", str(cls.repo), "update-ref", "HEAD", cls.sha], check=True, env=env)

    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="kiota-remote-test-")).resolve()
        self.binary = self.root / "fake-checker"
        self.binary.write_text(f"#!{sys.executable}\n" + FAKE)
        self.binary.chmod(0o700)
        self.manifest = {"repo_sha": self.sha, "inputs": []}
        self.args = SimpleNamespace(manifest=str(self.root / "manifest.json"),
                                    repo=str(self.repo), existing_checkout=str(self.repo),
                                    binary=str(self.binary), output_parent=str(self.root),
                                    total_timeout=15, build_timeout=2, memory_mib=None,
                                    log_bytes=runner.DEFAULT_LOG_BYTES, probe_perf=False)
        versions = patch.object(runner, "toolchain_preflight", return_value={"fixture": "no tool invocation"})
        self.toolchain_preflight = runner.toolchain_preflight
        versions.start()
        self.addCleanup(versions.stop)

    def case(self, payload=None, timeout=2):
        name = f"corpus-{len(self.manifest['inputs'])}"
        path = self.root / f"{name}.ndjson"
        raw = (json.dumps({"meta": HEADER}) + "\n" + json.dumps(payload or {}) + "\n").encode()
        path.write_bytes(raw)
        case = {"name": name, "path": path.name, "sha256": hashlib.sha256(raw).hexdigest(),
                "bytes": len(raw), "header": deepcopy(HEADER), "timeout": timeout}
        self.manifest["inputs"].append(case)
        return case, path

    def run_harness(self):
        Path(self.args.manifest).write_text(json.dumps(self.manifest))
        with redirect_stdout(io.StringIO()):
            code = runner.run(self.args)
        scratches = list(self.root.glob("kiota-remote-*"))
        self.assertEqual(len(scratches), 1)
        scratch = scratches[0]
        report = json.loads((scratch / "report.json").read_text())
        self.assertEqual(code, 0 if report["success"] else 1)
        return report, scratch

    def test_valid_header_all_accept_and_environment(self):
        self.case()
        self.case()
        with patch.dict(os.environ, {"KIOTA_SIZE_ONLY": "1", "KIOTA_MAX_DECL": "1",
                                     "KIOTA_NBE": "1", "KIOTA_RECLAIM": "1"}):
            report, scratch = self.run_harness()
        self.assertTrue(report["success"])
        self.assertTrue(report["complete"])
        self.assertEqual(report["kiota_environment"], {})
        self.assertEqual(report["binary_sha256"], hashlib.sha256(self.binary.read_bytes()).hexdigest())
        self.assertEqual(json.loads((scratch / "case-000.log").read_text()), {})
        self.assertEqual(report["checkout_before"]["actual_sha"], self.sha)
        self.assertFalse(json.loads((scratch / "provenance.json").read_text())["success"])
        self.assertFalse(report["source_build_association_verified"])
        self.assertFalse(report["public_candidate_gate"])
        self.assertIn("unverified", report["binary_source"])
        self.assertIn("cgroup", report["preflight"])
        self.assertEqual(report["limits"]["log_bytes"], 8 * 1024 * 1024)

    def test_reclaim_sets_only_one_kiota_variable(self):
        self.case()
        self.manifest["mode"] = "reclaim"
        with patch.dict(os.environ, {"KIOTA_SIZE_ONLY": "1", "KIOTA_NBE": "1"}):
            report, scratch = self.run_harness()
        self.assertTrue(report["success"])
        self.assertEqual(json.loads((scratch / "case-000.log").read_text()), {"KIOTA_RECLAIM": "1"})

    def test_distinct_outcomes_and_valid_corpora_require_accept(self):
        for code in range(5):
            self.case({"code": code})
        self.case({"signal": True})
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertTrue(report["complete"])
        self.assertEqual([c["outcome"] for c in report["cases"]],
                         ["accept", "reject", "decline", "error", "unexpected_exit", "crash"])
        self.assertEqual(report["cases"][-1]["exit_code"], -signal.SIGTERM)

    def test_all_inputs_preflight_before_any_checker(self):
        marker = self.root / "checker-ran"
        self.case({"marker": str(marker)})
        self.manifest["inputs"].append(dict(self.manifest["inputs"][0], name="missing", path="absent"))
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertFalse(report["complete"])
        self.assertEqual(report["cases"], [])
        self.assertFalse(marker.exists())
        self.assertIn("FileNotFoundError", report["error"])

    def test_sha_checkout_mismatch(self):
        self.case()
        self.manifest["repo_sha"] = "0" * 40
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertIn("checkout SHA mismatch", report["error"])
        self.assertEqual(report["cases"], [])

    def test_input_hash_and_header_mismatch(self):
        case, _ = self.case()
        case["sha256"] = "0" * 64
        report, _ = self.run_harness()
        self.assertIn("SHA-256 mismatch", report["error"])

    def test_header_version_mismatch(self):
        case, _ = self.case()
        case["header"]["lean"]["version"] = "wrong"
        report, _ = self.run_harness()
        self.assertIn("header mismatch", report["error"])

    def test_malformed_actual_header(self):
        case, path = self.case()
        raw = b'{"meta":{}}\n{}\n'
        path.write_bytes(raw)
        case.update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertIn("header requires", report["error"])

    def test_manifest_is_strict(self):
        self.case()
        valid = deepcopy(self.manifest)
        variants = []
        for key in ("name", "path", "sha256", "bytes", "header", "timeout"):
            item = deepcopy(valid)
            del item["inputs"][0][key]
            variants.append(item)
        for field, value in (("timeout", 3601), ("timeout", float("inf")), ("timeout", True),
                             ("sha256", None), ("bytes", 0), ("bytes", True)):
            item = deepcopy(valid)
            item["inputs"][0][field] = value
            variants.append(item)
        variants.extend(({"repo_sha": self.sha, "inputs": []},
                         dict(valid, repo_sha="main"), dict(valid, mode="nbe")))
        for item in variants:
            with self.subTest(item=item):
                Path(self.args.manifest).write_text(json.dumps(item))
                with self.assertRaises(ValueError):
                    runner.load_manifest(Path(self.args.manifest))
        with self.assertRaises(ValueError):
            runner.strict_json('{"a": 1, "a": 2}')

    def test_timeout_kills_process_group(self):
        marker = self.root / "child-survived"
        pidfile = self.root / "child.pid"
        self.case({"child": str(marker), "pidfile": str(pidfile), "sleep": 10}, timeout=2)
        report, _ = self.run_harness()
        self.assertEqual(report["cases"][0]["outcome"], "timeout")
        self.assertLess(report["cases"][0]["exit_code"], 0)
        self.assertTrue(pidfile.exists())
        time.sleep(1.1)
        self.assertFalse(marker.exists(), "descendant escaped timeout cleanup")
        pid = int(pidfile.read_text())
        proc_stat = Path(f"/proc/{pid}/stat")
        if proc_stat.exists():
            self.assertEqual(proc_stat.read_text().rsplit(")", 1)[1].split()[0], "Z")
        else:
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)

    def test_total_watchdog_never_reports_incomplete_success(self):
        self.case()
        self.case({"sleep": 10})
        self.case()
        self.args.total_timeout = .2
        with patch.object(runner, "verify_checkout", return_value={"actual_sha": self.sha}):
            report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertFalse(report["complete"])
        self.assertIn("total watchdog", report["error"])
        self.assertLess(len(report["cases"]), 3)
        self.assertEqual(report["cases"][-1]["outcome"], "total_timeout")

    def test_accepting_leader_with_live_child_is_incomplete(self):
        marker = self.root / "child-survived"
        self.case({"child": str(marker), "pidfile": str(self.root / "child.pid")})
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertEqual(report["cases"][0]["exit_code"], 0)
        self.assertEqual(report["cases"][0]["outcome"], "incomplete_process_group")

    def test_log_watchdog(self):
        self.case({"flood": True})
        self.args.log_bytes = 4096
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertEqual(report["cases"][0]["outcome"], "log_limit")

    def test_memory_watchdog(self):
        if not Path("/proc/self/statm").is_file():
            self.case()
            self.args.memory_mib = 1
            report, _ = self.run_harness()
            self.assertFalse(report["success"])
            self.assertIn("requires Linux", report["error"])
        else:
            result = runner.execute([sys.executable, "-c", "import time;time.sleep(1)"],
                                    self.root, runner.clean_environment("default"),
                                    self.root / "memory.log", 2, time.monotonic() + 3, memory_bytes=1)
            self.assertEqual(result["outcome"], "memory_limit")

    def test_input_change_during_checking_fails(self):
        _, path = self.case()
        raw = (json.dumps({"meta": HEADER}) + "\n" + json.dumps({"mutate": str(path)}) + "\n").encode()
        path.write_bytes(raw)
        self.manifest["inputs"][0].update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertEqual(report["cases"][0]["outcome"], "input_changed")

    def test_build_failure_is_checked_and_target_is_fresh(self):
        self.case()
        self.args.binary = None
        execute = runner.execute
        commands = []
        def fake_build(command, *args, **kwargs):
            commands.append(command)
            return execute([sys.executable, "-c", "import sys;sys.exit(1)"], *args, **kwargs)
        with patch.object(runner, "verify_checkout", return_value={"actual_sha": self.sha}), \
                patch.object(runner, "execute", side_effect=fake_build):
            report, scratch = self.run_harness()
        self.assertFalse(report["success"])
        self.assertEqual(report["cases"], [])
        self.assertIn("build failed", report["error"])
        self.assertIn("--offline", commands[0])
        self.assertIn("--locked", commands[0])
        self.assertEqual(commands[0][-1], str(scratch / "target"))

    def test_dirty_checkout_disallowed_for_build(self):
        with patch.object(runner, "git_read", side_effect=[self.sha, " M src/tc.rs"]):
            with self.assertRaisesRegex(ValueError, "local changes"):
                runner.verify_checkout(self.repo, self.sha, self.root, {}, time.monotonic() + 5, "x", True)

    def test_compiler_overrides_cleared_and_rustup_install_disabled(self):
        overrides = dict.fromkeys(runner.COMPILER_OVERRIDES, "inherited")
        overrides.update(CARGO_TARGET_TEST_RUSTFLAGS="inherited", RUSTUP_AUTO_INSTALL="1")
        with patch.dict(os.environ, overrides):
            env = runner.clean_environment("default")
        self.assertFalse(set(runner.COMPILER_OVERRIDES) & env.keys())
        self.assertNotIn("CARGO_TARGET_TEST_RUSTFLAGS", env)
        self.assertEqual(env["RUSTUP_AUTO_INSTALL"], "0")
        self.assertEqual(env["RUSTUP_SKIP_UPDATE_CHECK"], "1")

    def test_toolchain_versions_are_recorded_without_build(self):
        def version(command, cwd, env, log, *args, **kwargs):
            self.assertEqual(cwd, self.repo)
            self.assertEqual(command[-1], "--version")
            log.write_text(Path(command[0]).name + " test-version\n")
            return {"outcome": "accept", "exit_code": 0}
        with patch.object(runner.shutil, "which", side_effect=lambda tool: "/fake/" + tool), \
                patch.object(runner, "execute", side_effect=version):
            versions = self.toolchain_preflight(self.root, runner.clean_environment("default"),
                                               time.monotonic() + 2, cwd=self.repo)
        self.assertEqual(versions["rustc"]["version"], "rustc test-version")
        self.assertEqual(versions["cargo"]["version"], "cargo test-version")

    def test_cleanup_wait_is_bounded(self):
        proc = Mock(pid=999999)
        proc.poll.return_value = None
        proc.wait.side_effect = subprocess.TimeoutExpired(["fake"], 2)
        with patch.object(runner.subprocess, "Popen", return_value=proc), \
                patch.object(runner, "kill_group", return_value=True), \
                patch.object(runner, "child_finished_unreaped", return_value=False):
            result = runner.execute(["fake"], self.root, {}, self.root / "cleanup.log",
                                    .01, time.monotonic() + 1)
        proc.wait.assert_called_once_with(timeout=2)
        self.assertEqual(result["outcome"], "cleanup_failure")
        self.assertIsNone(result["exit_code"])

    def test_cleanup_failure_aborts_before_next_case_even_with_input_mutation(self):
        _, path = self.case()
        self.case()
        execute = runner.execute
        def cleanup_failed(command, *args, **kwargs):
            if command[-1] == "--use-stdin":
                path.write_bytes(path.read_bytes() + b" ")
                return {"outcome": "cleanup_failure", "exit_code": None}
            return execute(command, *args, **kwargs)
        with patch.object(runner, "execute", side_effect=cleanup_failed):
            report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertFalse(report["complete"])
        self.assertEqual(len(report["cases"]), 1)
        self.assertEqual(report["cases"][0]["outcome"], "cleanup_failure")
        self.assertTrue(report["cases"][0]["input_changed"])
        self.assertIn("no further cases", report["error"])

    def test_wait_probe_preserves_child_identity(self):
        with patch.object(runner.os, "waitid", return_value=SimpleNamespace(si_pid=123)) as peek:
            self.assertTrue(runner.child_finished_unreaped(123))
        self.assertTrue(peek.call_args.args[2] & os.WNOWAIT)

    def test_fresh_source_requires_toolchain_provenance(self):
        self.case()
        self.args.existing_checkout = None
        self.args.binary = None
        report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertFalse(report["public_candidate_gate"])
        self.assertIn("version probes", report["error"])
        self.assertEqual(report["cases"], [])

    def test_optional_perf_cleanup_failure_cannot_preserve_success(self):
        self.case()
        self.args.probe_perf = True
        with patch.object(runner, "perf_probe", side_effect=runner.CleanupFailure("probe cleanup")):
            report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertFalse(report["public_candidate_gate"])
        self.assertIn("CleanupFailure", report["error"])

    def test_toolchain_probe_cleanup_failure_is_fatal(self):
        with patch.object(runner.shutil, "which", return_value="/fake/rustc"), \
                patch.object(runner, "execute", return_value={"outcome": "cleanup_failure"}):
            with self.assertRaises(runner.CleanupFailure):
                self.toolchain_preflight(self.root, {}, time.monotonic() + 1)
        self.case()
        with patch.object(runner, "toolchain_preflight", side_effect=runner.CleanupFailure("probe cleanup")):
            report, _ = self.run_harness()
        self.assertFalse(report["success"])
        self.assertEqual(report["cases"], [])

    def test_existing_checkout_build_cannot_pass_public_candidate_gate(self):
        self.case()
        self.args.binary = None
        execute = runner.execute
        def build(command, *args, **kwargs):
            if command[0] == "cargo":
                target = Path(command[-1]) / "release"
                target.mkdir(parents=True)
                binary = target / "kiota"
                binary.write_bytes(self.binary.read_bytes())
                binary.chmod(0o700)
                return execute([sys.executable, "-c", "pass"], *args, **kwargs)
            return execute(command, *args, **kwargs)
        with patch.object(runner, "execute", side_effect=build):
            report, _ = self.run_harness()
        self.assertTrue(report["success"])
        self.assertFalse(report["source_build_association_verified"])
        self.assertFalse(report["public_candidate_gate"])

    def test_perf_unavailable_has_no_fake_zero(self):
        with patch.object(runner.shutil, "which", return_value=None):
            result = runner.perf_probe(self.root, {})
        self.assertEqual(result["status"], "unavailable")
        self.assertIsNone(result["instructions"])

    def test_perf_probe_checks_count_not_just_exit(self):
        for text, expected in (("<not counted>;;instructions;0;0\n", None),
                               ("0;;instructions;0;0\n", None),
                               ("12345;;instructions;100;50\n", None),
                               ("12345;;instructions;100;\n", None),
                               ("12345;;instructions:u;100;100\n", 12345)):
            scratch = Path(tempfile.mkdtemp(prefix="perf-", dir=self.root))
            def fake_perf(command, cwd, env, log, *args, **kwargs):
                log.write_text(text)
                return {"outcome": "accept", "exit_code": 0, "log": log.name}
            with patch.object(runner.shutil, "which", return_value="/fake/perf"), \
                    patch.object(runner, "execute", side_effect=fake_perf):
                result = runner.perf_probe(scratch, {})
            self.assertEqual(result["instructions"], expected)
            self.assertEqual(result["status"], "available" if expected else "unavailable")
            self.assertEqual(result["scope"], "probe only, not corpus ranking")
            if ";50;" in text:
                self.assertEqual(result["coverage_status"], "partial")
                self.assertEqual(result["running_percent"], 50)
            if expected:
                self.assertEqual(result["coverage_status"], "full")
                self.assertEqual(result["running_percent"], 100)

    def test_unique_scratch_and_exclusive_reports(self):
        self.case()
        first, scratch = self.run_harness()
        original = (scratch / "report.json").read_bytes()
        with self.assertRaises(FileExistsError):
            runner.write_json(scratch / "report.json", {})
        with redirect_stdout(io.StringIO()):
            self.assertEqual(runner.run(self.args), 0)
        self.assertEqual(len(list(self.root.glob("kiota-remote-*"))), 2)
        self.assertEqual((scratch / "report.json").read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
