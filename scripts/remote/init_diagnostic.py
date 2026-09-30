#!/usr/bin/env python3
"""Remote-only exact Init regeneration and bounded diagnostic, never a rank gate."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import sys
import tempfile
import time

if os.environ.get("GITHUB_ACTIONS") != "true" or platform.system() != "Linux" or platform.machine() != "x86_64":
    raise SystemExit("remote GitHub Linux runner required; no local execution")
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("remote_runner", ROOT / "scripts/remote/runner.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
ARENA = "cdb3497bd9080229f3ea107b0b9d5d25bd9e71a6"
EXPORTER = "66f1fb4bc256072069767fce52d39480e4524869"
CHECKER = "3260d921244ae3eca57b538dde72aad0357bef69"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
LEAN_SHA = "5045d0056413266e57c625dcd7c365b10e377c52"
INPUT_SHA = "620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a"
INPUT_BYTES, INPUT_LINES = 347555345, 6487065
IMAGE = "ubuntu@sha256:281c5745f657873d78e5531fc5ba8575f46ab7769b94550ac99543f122679986"
MIB = 1024 * 1024
temp_root = Path(os.environ["RUNNER_TEMP"]).resolve(strict=True)
if temp_root.is_symlink() or shutil.disk_usage(temp_root).free < 50 * 1024**3:
    raise SystemExit("require 50GiB free remote disk")
memory = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
if int(memory["MemAvailable"].split()[0]) < 12 * 1024**2:
    raise SystemExit("require 12GiB available remote RAM")
job = Path(tempfile.mkdtemp(prefix="kiota-exact-init-", dir=temp_root))
report_dir = ROOT / "init-report"
report_dir.mkdir(exist_ok=False)
logs = report_dir / "logs"
logs.mkdir()
env = runner.clean_environment("default")
env["ELAN_HOME"] = str(job / "elan")
env["PATH"] = str(job / "elan/bin") + os.pathsep + env["PATH"]
for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_GITHASH", "LAKE_OVERRIDE_LEAN", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"):
    env.pop(key, None)
deadline = time.monotonic() + 35 * 60
report = {"orchestration_revision": os.environ["GITHUB_SHA"], "checker_revision": CHECKER,
          "arena_revision": ARENA, "exporter_revision": EXPORTER,
          "full_corpus_verified": False, "arena_rank_verified": False,
          "init_input_verified": False, "init_accepted": False,
          "checker_started": False, "init_verdict": "not_run", "phases": []}
def save():
    (report_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while data := stream.read(MIB):
            digest.update(data)
    return digest.hexdigest()
def phase(label, command, seconds, cwd=ROOT):
    print("PHASE", label, flush=True)
    result = runner.execute(command, cwd, env, logs / (label + ".log"), seconds, (time.monotonic() + 30 if label == "container-stop" else deadline),
                            memory_bytes=12 * 1024**3, log_bytes=8 * MIB)
    runner.require_cleanup(result)
    report["phases"].append(dict(label=label, **result))
    save()
    print(json.dumps(result), flush=True)
    with (logs / result["log"]).open("rb") as stream:
        stream.seek(max(0, (logs / result["log"]).stat().st_size - 2048))
        print(stream.read().decode(errors="replace"), flush=True)
    if result["outcome"] != "accept":
        raise RuntimeError(label + ": " + result["outcome"])
def fetch(label, url, revision, directory):
    directory.mkdir(parents=True, exist_ok=False)
    phase(label + "-init", ["git", "init", "--quiet", str(directory)], 20)
    phase(label + "-origin", ["git", "-C", str(directory), "remote", "add", "origin", url], 20)
    phase(label + "-fetch", ["git", "-C", str(directory), "fetch", "--no-tags", "--depth=1", "origin", revision], 180)
    phase(label + "-checkout", ["git", "-C", str(directory), "checkout", "--quiet", "--detach", "FETCH_HEAD"], 20)
    phase(label + "-pin", ["git", "-C", str(directory), "show", "--format=%H", "--no-patch", "HEAD"], 20)
    if (logs / (label + "-pin.log")).read_text().strip() != revision:
        raise RuntimeError("source revision mismatch")
def download(label, url, destination):
    phase(label, ["curl", "--fail", "--location", "--retry", "2", "--max-time", "180",
                  "--proto", "=https", "--output", str(destination), url], 210)
cid = None
save()
try:
    for executable in ("git", "curl", "tar", "uv", "cargo", "rustc", "docker", "/usr/bin/time"):
        if not shutil.which(executable):
            raise RuntimeError("missing remote executable: " + executable)
    phase("rust-toolchain", ["rustc", "--version", "--verbose"], 20)
    installer = job / "elan.tar.gz"
    download("elan-download", "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz", installer)
    if sha(installer) != "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63":
        raise RuntimeError("elan installer checksum mismatch")
    unpack = job / "elan-installer"
    unpack.mkdir()
    phase("elan-unpack", ["tar", "-xzf", str(installer), "-C", str(unpack)], 30)
    phase("elan-install", [str(unpack / "elan-init"), "-y", "--no-modify-path", "--default-toolchain", "none"], 120)
    phase("lean-install", ["elan", "toolchain", "install", TOOLCHAIN], 480)
    phase("lean-version", ["elan", "run", TOOLCHAIN, "lean", "--version"], 30)
    arena = job / "arena"
    fetch("arena", "https://github.com/leanprover/lean-kernel-arena", ARENA, arena)
    exporter = arena / "_build/lean4export/leanprover_lean4_v4.34.1"
    fetch("exporter", "https://github.com/leanprover/lean4export", EXPORTER, exporter)
    (exporter / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    phase("exporter-build", ["lake", "build"], 300, exporter)
    phase("init-generation", ["uv", "run", "lka.py", "build-test", "init"], 900, arena)
    source = arena / "_build/tests/init.ndjson"
    stats = json.loads((arena / "_build/tests/init.stats.json").read_text())
    with source.open("rb") as stream:
        header = json.loads(stream.readline())
        stream.seek(0)
        lines = sum(chunk.count(b"\n") for chunk in iter(lambda: stream.read(MIB), b""))
    actual_sha = sha(source)
    if actual_sha != INPUT_SHA or source.stat().st_size != INPUT_BYTES or lines != INPUT_LINES:
        raise RuntimeError("generated Init bytes do not match official target")
    meta = header["meta"]
    if meta["lean"] != {"version": "4.34.1", "githash": LEAN_SHA} or meta["exporter"] != {"name": "lean4export", "version": "3.1.0"}:
        raise RuntimeError("wrong Lean/exporter header")
    expected = {"name": "init", "sha256": INPUT_SHA, "size": INPUT_BYTES, "lines": INPUT_LINES,
                "lean_version": "4.34.1", "lean_githash": LEAN_SHA, "lean4export_version": "3.1.0"}
    if any(stats.get(key) != value for key, value in expected.items()):
        raise RuntimeError("generated statistics mismatch")
    publication = job / "current-results.json"
    download("current-publication", "https://arena.lean-lang.org/results.json", publication)
    tests = [test for test in json.loads(publication.read_text())["tests"] if test["name"] == "init"]
    if len(tests) != 1 or any(tests[0].get(key) != value for key, value in expected.items()):
        raise RuntimeError("current official Init differs; checker will not run")
    report.update(init_input_verified=True, input_sha256=actual_sha, input_header=header,
                  input_bytes=INPUT_BYTES, input_lines=INPUT_LINES)
    (report_dir / "input.stats.json").write_text(json.dumps(stats, indent=2) + "\n")
    checker = job / "checker"
    fetch("checker", "https://github.com/sankalpsthakur/kiota", CHECKER, checker)
    phase("checker-build", ["cargo", "build", "--release", "--locked", "--jobs", "2"], 300, checker)
    phase("checker-clean", ["git", "diff", "--exit-code"], 20, checker)
    phase("checker-index-clean", ["git", "diff", "--cached", "--exit-code"], 20, checker)
    binary = checker / "target/release/kiota"
    report.update(binary_sha256=sha(binary), cargo_lock_sha256=sha(checker / "Cargo.lock"))
    phase("container-image", ["docker", "pull", IMAGE], 180)
    phase("container-create", ["docker", "create", "--init", "--network", "none", "--read-only",
          "--cap-drop", "ALL", "--security-opt", "no-new-privileges", "--pids-limit", "64",
          "--memory", str(6 * 1024**3), "--memory-swap", str(6 * 1024**3),
          "--log-driver", "local", "--log-opt", "max-size=1m", "--log-opt", "max-file=1",
          "--log-opt", "compress=false",
          "--user", str(os.getuid()) + ":" + str(os.getgid()),
          "--env", "KIOTA_PROGRESS=1",
          "--mount", "type=bind,src=" + str(binary) + ",dst=/checker,readonly",
          "--mount", "type=bind,src=" + str(source) + ",dst=/input,readonly",
          "--mount", "type=bind,src=/usr/bin/time,dst=/time,readonly",
          "--mount", "type=bind,src=" + str(report_dir) + ",dst=/out",
          IMAGE, "/bin/sh", "-ec",
          'test "$(cat /sys/fs/cgroup/memory.max)" = 6442450944; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; exec /time -v -o /out/checker.time /usr/bin/timeout --signal=TERM --kill-after=5s 600s /checker /input'], 30)
    cid = (logs / "container-create.log").read_text().strip()
    if len(cid) != 64 or any(char not in "0123456789abcdef" for char in cid):
        raise RuntimeError("unexpected container identity")
    diagnostic = runner.execute(["docker", "start", "--attach", cid], ROOT, env,
          logs / "init-diagnostic.log", 630, deadline, memory_bytes=12 * 1024**3, log_bytes=8 * MIB)
    runner.require_cleanup(diagnostic)
    report["diagnostic"] = diagnostic
    with (logs / "init-diagnostic.log").open("rb") as stream:
        stream.seek(max(0, (logs / "init-diagnostic.log").stat().st_size - 8192))
        print(stream.read().decode(errors="replace"), flush=True)
    phase("container-state", ["docker", "inspect", "--format", "{{json .State}}", cid], 20)
    state = json.loads((logs / "container-state.log").read_text())
    report["container_state"] = state
    report["checker_started"] = state["StartedAt"] != "0001-01-01T00:00:00Z" and not state["Error"]
    if not report["checker_started"]:
        raise RuntimeError("checker never started: " + state["Error"])
    if state["Running"]:
        raise RuntimeError("checker container still running")
    if sha(binary) != report["binary_sha256"] or sha(source) != actual_sha:
        raise RuntimeError("input/binary changed during run")
    phase("checker-post-clean", ["git", "diff", "--exit-code"], 20, checker)
    phase("checker-post-index-clean", ["git", "diff", "--cached", "--exit-code"], 20, checker)
    report["init_accepted"] = diagnostic["outcome"] == "accept" and state["ExitCode"] == 0 and not state["OOMKilled"] and not state["Error"]
    report["init_verdict"] = ("accept" if report["init_accepted"] else
                              "memory_limit" if state["OOMKilled"] else
                              "timeout" if state["ExitCode"] in (124, 137) else
                              diagnostic["outcome"])
except Exception as error:
    report["error"] = str(error)
finally:
    if cid and len(cid) == 64 and all(char in "0123456789abcdef" for char in cid):
        try:
            phase("container-stop", ["docker", "stop", "--time", "5", cid], 20)
        except Exception as error:
            report["cleanup_error"] = str(error)
            report["init_accepted"] = False
    save()
print(json.dumps(report), flush=True)
raise SystemExit(0 if report["init_accepted"] else 1)
