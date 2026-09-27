#!/usr/bin/env python3
"""Offline, fail-closed verification of pre-existing large Lean exports (POSIX)."""
from __future__ import annotations

import argparse
from contextlib import ExitStack
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time

HEADER_LIMIT = 64 * 1024
CHUNK = 1024 * 1024
POLL = 0.02


class CleanupFailure(RuntimeError):
    pass


def require_cleanup(result):
    if result["outcome"] in ("cleanup_failure", "incomplete_process_group"):
        raise CleanupFailure(f"unsafe process cleanup: {result['outcome']}")
DEFAULT_LOG_BYTES = 8 * 1024 * 1024
COMPILER_OVERRIDES = {"RUSTC", "RUSTDOC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                      "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS",
                      "CARGO_ENCODED_RUSTDOCFLAGS", "CARGO_BUILD_RUSTFLAGS",
                      "CARGO_BUILD_RUSTDOCFLAGS", "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTDOC",
                      "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"}


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs,
                      parse_constant=lambda value: fail(f"nonfinite JSON: {value}"))


def fail(message):
    raise ValueError(message)


def bounded_number(value, label, maximum=None):
    if (type(value) not in (int, float) or not math.isfinite(value)
            or value <= 0 or (maximum is not None and value > maximum)):
        fail(f"{label} must be positive, finite" + (f" and <= {maximum}" if maximum else ""))
    return value


def nonempty(value, label):
    if not isinstance(value, str) or not value.strip() or "\0" in value:
        fail(f"{label} must be a nonempty string")
    return value


def hex_value(value, length, label):
    if not isinstance(value, str) or not re.fullmatch(rf"[0-9a-fA-F]{{{length}}}", value):
        fail(f"{label} must be exactly {length} hex characters")
    return value.lower()


def validate_header(header):
    if not isinstance(header, dict) or set(header) != {"lean", "exporter", "format"}:
        fail("header requires lean, exporter, format objects")
    for section, keys in (("lean", ("version", "githash")),
                          ("exporter", ("name", "version")), ("format", ("version",))):
        if not isinstance(header[section], dict):
            fail(f"header.{section} must be an object")
        for key in keys:
            nonempty(header[section].get(key), f"header.{section}.{key}")


def load_manifest(path):
    with path.open("rb") as stream:
        raw = stream.read(CHUNK + 1)
    if len(raw) > CHUNK:
        fail("manifest exceeds 1 MiB")
    manifest = strict_json(raw)
    if not isinstance(manifest, dict) or set(manifest) - {"repo_sha", "mode", "inputs"}:
        fail("manifest keys: repo_sha, mode, inputs")
    manifest["repo_sha"] = hex_value(manifest.get("repo_sha"), 40, "repo_sha")
    manifest.setdefault("mode", "default")
    if manifest["mode"] not in ("default", "reclaim"):
        fail("mode must be default or reclaim")
    inputs = manifest.get("inputs")
    if not isinstance(inputs, list) or not 1 <= len(inputs) <= 256:
        fail("inputs must contain 1..256 valid corpora")
    names = set()
    for case in inputs:
        if not isinstance(case, dict) or set(case) != {"name", "path", "sha256", "bytes", "header", "timeout"}:
            fail("input keys: name, path, sha256, bytes, header, timeout")
        name = nonempty(case["name"], "input.name")
        if name in names:
            fail(f"duplicate input name: {name}")
        names.add(name)
        nonempty(case["path"], "input.path")
        case["sha256"] = hex_value(case["sha256"], 64, "input.sha256")
        if type(case["bytes"]) is not int or case["bytes"] <= 0:
            fail("input.bytes must be a positive integer")
        bounded_number(case["timeout"], "input.timeout", 3600)
        validate_header(case["header"])
    return manifest, hashlib.sha256(raw).hexdigest()


def check_deadline(deadline):
    if time.monotonic() >= deadline:
        fail("total watchdog expired")


def identity(stream):
    info = os.fstat(stream.fileno())
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def file_hash(stream, deadline):
    digest = hashlib.sha256()
    for chunk in iter(lambda: stream.read(CHUNK), b""):
        check_deadline(deadline)
        digest.update(chunk)
    check_deadline(deadline)
    return digest.hexdigest()


def verify_input(case, base, stack, deadline):
    path = (base / case["path"]).resolve(strict=True)
    # Nonblocking open prevents a FIFO/device from defeating the supervisor.
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
    stream = stack.enter_context(os.fdopen(fd, "rb"))
    if not stat.S_ISREG(os.fstat(fd).st_mode):
        fail(f"{case['name']}: input is not a regular file")
    before = identity(stream)
    if before[2] != case["bytes"]:
        fail(f"{case['name']}: byte count mismatch")
    line = stream.readline(HEADER_LIMIT + 1)
    if len(line) > HEADER_LIMIT or not line.endswith(b"\n"):
        fail(f"{case['name']}: missing or oversized header line")
    actual = strict_json(line)
    if not isinstance(actual, dict) or set(actual) != {"meta"}:
        fail(f"{case['name']}: first line must contain only meta")
    validate_header(actual["meta"])
    if actual["meta"] != case["header"]:
        fail(f"{case['name']}: header mismatch")
    stream.seek(0)
    if file_hash(stream, deadline) != case["sha256"]:
        fail(f"{case['name']}: SHA-256 mismatch")
    if identity(stream) != before:
        fail(f"{case['name']}: input changed while hashing")
    stream.seek(0)
    return stream, before, str(path)


def clean_environment(mode):
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("KIOTA_", "GIT_")) and k not in COMPILER_OVERRIDES
           and not (k.startswith("CARGO_TARGET_") and k.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))}
    env.update(RUSTUP_AUTO_INSTALL="0", RUSTUP_SKIP_UPDATE_CHECK="1")
    if mode == "reclaim":
        env["KIOTA_RECLAIM"] = "1"
    return env


def group_rss_bytes(group):
    """Linux sampled group RSS; shared pages may be counted more than once."""
    total = 0
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == group:
                total += int((entry / "statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE")
        except (FileNotFoundError, ProcessLookupError):
            continue
    return total


def kill_group(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
        return True
    except ProcessLookupError:
        return False


def child_finished_unreaped(pid):
    # Leave the direct child unreaped until group signalling is finished. Its
    # PID/PGID cannot be recycled while the parent still owns this wait record.
    result = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    return result is not None and result.si_pid == pid


def group_has_descendants(pid):
    rows = subprocess.check_output(["ps", "-axo", "pid=,pgid="], text=True, timeout=2)
    return any(int(parts[1]) == pid and int(parts[0]) != pid
               for row in rows.splitlines() if len(parts := row.split()) == 2)


def execute(command, cwd, env, log, timeout, deadline, stdin=None,
            memory_bytes=None, log_bytes=None):
    check_deadline(deadline)
    started = time.monotonic()
    cutoff = min(deadline, started + timeout)
    reason = None
    cleanup_error = None
    peak = None
    owned_wait_record = True
    with log.open("xb") as output:
        proc = subprocess.Popen(command, cwd=cwd, env=env,
                                stdin=stdin if stdin is not None else subprocess.DEVNULL,
                                stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while True:
                now = time.monotonic()
                if now >= cutoff:
                    reason = "total_timeout" if deadline <= started + timeout else "timeout"
                if log_bytes is not None and os.fstat(output.fileno()).st_size > log_bytes:
                    reason = "log_limit"
                if memory_bytes is not None:
                    peak = max(peak or 0, group_rss_bytes(proc.pid))
                    if peak > memory_bytes:
                        reason = "memory_limit"
                try:
                    finished = child_finished_unreaped(proc.pid)
                except ChildProcessError:
                    owned_wait_record = False
                    reason = "cleanup_failure"
                    cleanup_error = "child wait record was lost; group signalling refused"
                    break
                if reason or finished:
                    break
                time.sleep(min(POLL, max(0, cutoff - now)))
        finally:
            # Includes descendants surviving an otherwise normal leader exit.
            try:
                survivors = (group_has_descendants(proc.pid)
                             if owned_wait_record and reason is None else False)
                if owned_wait_record and (reason is not None or survivors):
                    kill_group(proc.pid)
            except (OSError, subprocess.SubprocessError) as exc:
                survivors = True
                reason, cleanup_error = "cleanup_failure", str(exc)
            try:
                returncode = proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                reason, cleanup_error = "cleanup_failure", "process did not reap within 2 seconds"
                returncode = None
        if reason is None and survivors:
            reason = "incomplete_process_group"
        if log_bytes is not None and os.fstat(output.fileno()).st_size > log_bytes:
            reason = reason or "log_limit"
    outcome = reason or ({0: "accept", 1: "reject", 2: "decline", 3: "error"}.get(returncode)
                         or ("crash" if returncode < 0 else "unexpected_exit"))
    return {"command": command, "exit_code": returncode, "outcome": outcome,
            "wall_seconds": time.monotonic() - started, "peak_sampled_rss_bytes": peak,
            "log": log.name, "cleanup_error": cleanup_error}


def git_read(checkout, args, scratch, env, deadline, label):
    log = scratch / f"git-{label}.log"
    result = execute(["git", "-c", "core.hooksPath=/dev/null", "-C", str(checkout), *args],
                     scratch, env, log, 60, deadline, log_bytes=CHUNK)
    if result["outcome"] != "accept":
        fail(f"git {label} failed: {result['outcome']}; see {log.name}")
    with log.open("rb") as stream:
        return stream.read(CHUNK).decode("utf-8", "strict").strip()


def verify_checkout(checkout, sha, scratch, env, deadline, label, require_clean):
    actual = git_read(checkout, ["rev-parse", "--verify", "HEAD"], scratch, env, deadline, label + "-sha")
    if actual != sha:
        fail(f"checkout SHA mismatch: expected {sha}, actual {actual}")
    dirty = git_read(checkout, ["status", "--porcelain", "--untracked-files=all"],
                     scratch, env, deadline, label + "-status")
    if require_clean and dirty:
        fail("immutable checkout has local changes")
    return {"actual_sha": actual, "dirty_status": dirty}


def write_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")


def machine_preflight(scratch):
    result = {"cpu_count": os.cpu_count(), "disk_free_bytes": shutil.disk_usage(scratch).free,
              "cgroup": {"status": "unavailable"}}
    if hasattr(os, "sched_getaffinity"):
        result["cpu_affinity"] = sorted(os.sched_getaffinity(0))
    def read_small(path):
        try:
            with path.open("rb") as stream:
                return stream.read(16384).decode("utf-8", "replace").strip()
        except OSError:
            return None
    result["meminfo"] = read_small(Path("/proc/meminfo"))
    membership = read_small(Path("/proc/self/cgroup"))
    result["cgroup"]["membership"] = membership
    if membership:
        base = Path("/sys/fs/cgroup").resolve()
        for line in membership.splitlines():
            if line.startswith("0::"):
                directory = (base / line[3:].lstrip("/")).resolve()
                if not directory.is_relative_to(base):
                    continue
                values = {name: read_small(directory / name) for name in
                          ("memory.max", "memory.current", "memory.swap.max", "cpu.max", "pids.max")}
                result["cgroup"].update(status="v2" if any(v is not None for v in values.values())
                                       else "unavailable", path=str(directory), limits=values)
    return result


def toolchain_preflight(scratch, env, deadline, cwd=None):
    versions = {}
    for tool in ("rustc", "cargo"):
        path = shutil.which(tool)
        if path is None:
            versions[tool] = {"status": "unavailable", "version": None}
            continue
        log = scratch / f"{tool}-version.log"
        try:
            result = execute([path, "--version"], cwd or scratch, env, log, 5, deadline, log_bytes=HEADER_LIMIT)
            require_cleanup(result)
            with log.open("rb") as stream:
                version = stream.read(HEADER_LIMIT).decode("utf-8", "replace").strip()
            versions[tool] = {"status": "available" if result["outcome"] == "accept" else "unavailable",
                              "version": version or None, "execution": result}
        except OSError as exc:
            versions[tool] = {"status": "unavailable", "version": None, "reason": str(exc)}
    return versions


def perf_probe(scratch, env, deadline=None):
    perf = shutil.which("perf")
    result = {"status": "unavailable", "instructions": None, "running_percent": None,
              "coverage_status": "unavailable", "event": None,
              "event_scope": None, "scope": "probe only, not corpus ranking"}
    if perf is None:
        result["reason"] = "perf executable not found"
        return result
    measured = execute([perf, "stat", "-x", ";", "-e", "instructions", "--",
                        sys.executable, "-c", "pass"], scratch, env, scratch / "perf-probe.log",
                       10, deadline if deadline is not None else time.monotonic() + 10,
                       log_bytes=HEADER_LIMIT)
    require_cleanup(measured)
    result["execution"] = measured
    with (scratch / "perf-probe.log").open("rb") as stream:
        raw = stream.read(HEADER_LIMIT).decode("utf-8", "replace")
    if measured["outcome"] == "accept":
        for line in raw.splitlines():
            fields = line.split(";")
            if len(fields) >= 3 and fields[2].strip().split(":")[0] == "instructions":
                result["event"] = fields[2].strip()
                result["event_scope"] = ("user-only" if ":u" in result["event"]
                                         else "as configured by perf/kernel")
                result["coverage_status"] = "invalid"
                if len(fields) < 5:
                    continue
                try:
                    count = int(fields[0].strip())
                    runtime = float(fields[3].strip())
                    percent = float(fields[4].strip())
                except ValueError:
                    continue
                result["running_percent"] = percent if math.isfinite(percent) else None
                if not math.isfinite(runtime) or runtime <= 0 or not math.isfinite(percent) or not 0 < percent <= 100:
                    continue
                result["coverage_status"] = "full" if percent == 100 else "partial"
                if count > 0 and percent == 100:
                    result.update(status="available", instructions=count)
    if result["status"] == "unavailable":
        result["reason"] = "no positive instruction count at 100% running coverage; inspect probe log"
    return result


def run(args):
    scratch = Path(tempfile.mkdtemp(prefix="kiota-remote-", dir=args.output_parent)).resolve()
    started = time.monotonic()
    deadline = started + args.total_timeout
    report = {"schema": 1, "success": False, "complete": False, "public_candidate_gate": False,
              "scope": "listed manifest inputs only", "full_arena_coverage_verified": False,
              "arena_rank_verified": False,
              "source_build_association_verified": False, "scratch": str(scratch),
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "host": list(os.uname()), "python": sys.version,
              "limits": {k: getattr(args, k) for k in
                         ("total_timeout", "build_timeout", "memory_mib", "log_bytes")},
              "cases": [], "error": None, "perf": {"status": "not_requested", "instructions": None}}
    print(f"scratch: {scratch}", flush=True)
    try:
        with ExitStack() as stack:
            manifest_path = Path(args.manifest).resolve(strict=True)
            manifest, manifest_hash = load_manifest(manifest_path)
            report.update(manifest=manifest, manifest_sha256=manifest_hash,
                          expected_cases=len(manifest["inputs"]))
            env = clean_environment(manifest["mode"])
            report["preflight"] = machine_preflight(scratch)
            report["removed_compiler_overrides"] = sorted(k for k in os.environ
                                                          if k not in env and not k.startswith(("GIT_", "KIOTA_")))
            report["rustup_environment"] = {k: env[k] for k in ("RUSTUP_AUTO_INSTALL", "RUSTUP_SKIP_UPDATE_CHECK")}
            report["kiota_environment"] = {k: v for k, v in env.items() if k.startswith("KIOTA_")}
            report["removed_kiota_variables"] = sorted(k for k in os.environ if k.startswith("KIOTA_"))
            if args.memory_mib is not None and not Path("/proc/self/statm").is_file():
                fail("memory watchdog requires Linux /proc; requested limit cannot be enforced")
            # Keep the verified regular-file descriptors pinned through checking.
            verified = [verify_input(case, manifest_path.parent, stack, deadline)
                        for case in manifest["inputs"]]
            report["validated_inputs"] = [dict(case, resolved_path=item[2])
                                          for case, item in zip(manifest["inputs"], verified)]
            if args.existing_checkout:
                checkout = Path(args.existing_checkout).resolve(strict=True)
            else:
                source = Path(args.repo).resolve(strict=True)
                checkout = scratch / "checkout"
                result = execute(["git", "clone", "--local", "--no-hardlinks", "--no-checkout",
                                  "--", str(source), str(checkout)], scratch, env,
                                 scratch / "clone.log", args.build_timeout, deadline,
                                 log_bytes=args.log_bytes)
                report["clone"] = result
                if result["outcome"] != "accept":
                    fail(f"local clone failed: {result['outcome']}")
                git_read(checkout, ["checkout", "--detach", manifest["repo_sha"]],
                         scratch, env, deadline, "detach")
            report["checkout"] = str(checkout)
            report["checkout_before"] = verify_checkout(checkout, manifest["repo_sha"], scratch,
                                                        env, deadline, "before", not args.binary)
            report["toolchain"] = toolchain_preflight(scratch, env, deadline, cwd=checkout)
            if not args.binary and not args.existing_checkout:
                if any(report["toolchain"].get(tool, {}).get("status") != "available"
                       for tool in ("rustc", "cargo")):
                    fail("fresh source validation requires available Rust/Cargo version probes")
            if args.binary:
                binary = Path(args.binary).resolve(strict=True)
                report["binary_source"] = "provided: local tests only; source/build association unverified"
            else:
                target = scratch / "target"
                command = ["cargo", "build", "--offline", "--locked", "--release", "--bin", "kiota",
                           "--target-dir", str(target)]
                report["build"] = execute(command, checkout, env, scratch / "build.log",
                                          args.build_timeout, deadline, log_bytes=args.log_bytes)
                if report["build"]["outcome"] != "accept":
                    fail(f"build failed: {report['build']['outcome']}")
                binary = target / "release" / "kiota"
                report["binary_source"] = ("fresh offline locked build from immutable clone" if not args.existing_checkout
                                           else "existing checkout build: source association unverified")
            if not binary.is_file() or not os.access(binary, os.X_OK):
                fail("binary missing or not executable")
            with binary.open("rb") as stream:
                binary_hash = file_hash(stream, deadline)
                binary_identity = identity(stream)
            report.update(binary=str(binary), binary_sha256=binary_hash)
            write_json(scratch / "provenance.json", report)
            for ordinal, (case, (stream, before, _)) in enumerate(zip(manifest["inputs"], verified)):
                check_deadline(deadline)
                if identity(stream) != before:
                    fail(f"{case['name']}: input changed before checking")
                result = execute([str(binary), "--use-stdin"], checkout, env,
                                 scratch / f"case-{ordinal:03d}.log", case["timeout"], deadline,
                                 stdin=stream, memory_bytes=(args.memory_mib * CHUNK if args.memory_mib else None),
                                 log_bytes=args.log_bytes)
                result.update(name=case["name"], expected_exit=0, sha256=case["sha256"])
                if identity(stream) != before:
                    result["input_changed"] = True
                    if result["outcome"] not in ("cleanup_failure", "incomplete_process_group"):
                        result["outcome"] = "input_changed"
                result["passed"] = result["outcome"] == "accept" and result["exit_code"] == 0
                report["cases"].append(result)
                if result["outcome"] in ("cleanup_failure", "incomplete_process_group"):
                    fail(f"{case['name']}: incomplete process cleanup; no further cases launched")
            report["checkout_after"] = verify_checkout(checkout, manifest["repo_sha"], scratch,
                                                       env, deadline, "after", not args.binary)
            with binary.open("rb") as stream:
                if identity(stream) != binary_identity or file_hash(stream, deadline) != binary_hash:
                    fail("binary changed during checking")
            if any(identity(stream) != before for stream, before, _ in verified):
                fail("verified input changed during the run")
            check_deadline(deadline)
            report["complete"] = len(report["cases"]) == len(manifest["inputs"])
            report["success"] = report["complete"] and all(c["passed"] for c in report["cases"])
            if args.probe_perf:
                # Separate optional probe: never converts correctness failure into success.
                try:
                    report["perf"] = perf_probe(scratch, env, deadline)
                except (OSError, ValueError) as exc:
                    report["perf"] = {"status": "unavailable", "instructions": None, "reason": str(exc)}
                check_deadline(deadline)
            associated = not bool(args.binary or args.existing_checkout)
            report["source_build_association_verified"] = associated
            report["public_candidate_gate"] = report["success"] and associated
    except (OSError, ValueError, CleanupFailure, KeyboardInterrupt) as exc:
        report.update(success=False, complete=False, public_candidate_gate=False,
                      error=f"{type(exc).__name__}: {exc}")
    finally:
        report["wall_seconds"] = time.monotonic() - started
        write_json(scratch / "report.json", report)
    print(f"{'PASS' if report['success'] else 'FAIL'}: {scratch / 'report.json'}", flush=True)
    return 0 if report["success"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest")
    parser.add_argument("--repo", default=str(Path(__file__).resolve().parents[2]),
                        help="local repository used for an offline, detached clone")
    parser.add_argument("--existing-checkout", help="explicit existing checkout (must match SHA)")
    parser.add_argument("--binary", help="test binary; requires --existing-checkout")
    parser.add_argument("--output-parent", help="existing directory for a new unique scratch")
    parser.add_argument("--total-timeout", type=float, default=14400)
    parser.add_argument("--build-timeout", type=float, default=1800)
    parser.add_argument("--memory-mib", type=int, help="Linux sampled process-group RSS watchdog")
    parser.add_argument("--log-bytes", type=int, default=DEFAULT_LOG_BYTES,
                        help="sampled per-command log size watchdog (default: 8 MiB)")
    parser.add_argument("--probe-perf", action="store_true")
    args = parser.parse_args()
    try:
        bounded_number(args.total_timeout, "total timeout")
        bounded_number(args.build_timeout, "build timeout", 3600)
        for label in ("memory_mib", "log_bytes"):
            if getattr(args, label) is not None:
                bounded_number(getattr(args, label), label)
        if args.binary and not args.existing_checkout:
            fail("--binary requires explicit --existing-checkout")
        if os.name != "posix":
            fail("POSIX process groups required")
        if not all(hasattr(os, key) for key in ("waitid", "WNOWAIT", "P_PID")):
            fail("unreaped child inspection (waitid/WNOWAIT) is required")
    except ValueError as exc:
        parser.error(str(exc))
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
