#!/usr/bin/env python3
"""Strict, offline runner for Arena's small-test tarball; not a full-corpus claim."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import resource
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
from typing import Any

MAX_MEMBER_BYTES = 16 * 1024 * 1024
MAX_TOTAL_BYTES = 512 * 1024 * 1024
MAX_MEMBERS = 10_000


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def unpack_cases(archive: Path, destination: Path) -> list[tuple[str, int, Path]]:
    """Copy only regular good/bad test files; never extract links or paths."""
    cases: list[tuple[str, int, Path]] = []
    seen: set[str] = set()
    total = 0
    with tarfile.open(archive, "r:gz") as bundle:
        for index, member in enumerate(bundle):
            if index >= MAX_MEMBERS:
                raise ValueError("archive has too many members")
            name = PurePosixPath(member.name)
            if name.is_absolute() or ".." in name.parts or "\\" in member.name:
                raise ValueError(f"unsafe archive path: {member.name}")
            if member.isdir():
                continue
            if not member.isfile():
                raise ValueError(f"non-regular archive member: {member.name}")
            if len(name.parts) < 2 or name.parts[0] not in {"good", "bad"}:
                raise ValueError(f"unrecognized test member: {member.name}")
            canonical = name.as_posix()
            if canonical in seen:
                raise ValueError(f"duplicate test member: {canonical}")
            seen.add(canonical)
            total += member.size
            if member.size < 0 or member.size > MAX_MEMBER_BYTES or total > MAX_TOTAL_BYTES:
                raise ValueError("archive exceeds the small-suite size budget")
            source = bundle.extractfile(member)
            if source is None:
                raise ValueError(f"unreadable member: {canonical}")
            with source:
                payload = source.read(MAX_MEMBER_BYTES + 1)
            if len(payload) != member.size:
                raise ValueError(f"incomplete member: {canonical}")
            target = destination / f"{len(cases):05d}.ndjson"
            target.write_bytes(payload)
            cases.append((canonical, 0 if name.parts[0] == "good" else 1, target))
    if not cases:
        raise ValueError("archive contains no test cases")
    return sorted(cases)


def classify(returncode: int | None, timed_out: bool) -> str:
    if timed_out:
        return "timeout"
    return {0: "accept", 1: "reject", 2: "decline", 3: "error"}.get(returncode, "crash")


def exec_limited(memory_mib: int, binary: str, case: str) -> None:
    """Limit the child, not the supervisor. No threaded-fork preexec hook."""
    limit = memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_FSIZE, (64 * 1024 * 1024, 64 * 1024 * 1024))
    os.execv(binary, [binary, case])


def write_report(output: Path, report: dict[str, Any]) -> None:
    temporary = output / "report.json.tmp"
    temporary.write_text(json.dumps(report, indent=2) + "\n")
    temporary.replace(output / "report.json")


def run_case(binary: Path, case: tuple[str, int, Path], mode: str,
             timeout: float, log_dir: Path, ordinal: int,
             memory_mib: int = 4096) -> dict[str, Any]:
    name, expected, path = case
    env = {key: value for key, value in os.environ.items() if not key.startswith("KIOTA_")}
    if mode == "nbe":
        env["KIOTA_NBE"] = "1"
    log = log_dir / f"{mode}-{ordinal:05d}.log"
    started = time.monotonic()
    timed_out = False
    command = [sys.executable, str(Path(__file__).resolve()), "--exec-limited",
               str(memory_mib), str(binary), str(path)]
    with log.open("wb") as output:
        proc = subprocess.Popen(command, env=env, stdin=subprocess.DEVNULL,
                                stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            returncode = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            returncode = proc.wait()
    outcome = classify(returncode, timed_out)
    result = {"test": name, "test_sha256": sha256_file(path), "mode": mode,
              "expected": "accept" if expected == 0 else "reject", "outcome": outcome,
              "exit_code": returncode, "passed": not timed_out and returncode == expected,
              "wall_seconds": round(time.monotonic() - started, 6), "log": log.name}
    if not result["passed"]:
        with log.open("rb") as stream:
            stream.seek(max(0, log.stat().st_size - 2048))
            result["diagnostic_tail"] = stream.read().decode("utf-8", errors="replace")
    return result


def run_gate(binary: Path, archive: Path, output: Path, modes: list[str], timeout: float,
             min_good: int, min_bad: int, memory_mib: int = 4096) -> dict[str, Any]:
    binary, archive = binary.resolve(strict=True), archive.resolve(strict=True)
    if not os.access(binary, os.X_OK):
        raise ValueError("binary is not executable")
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("timeout must be finite and positive")
    if min_good < 1 or min_bad < 1:
        raise ValueError("minimum good and bad counts must both be positive")
    if not modes or any(mode not in {"default", "nbe"} for mode in modes):
        raise ValueError("invalid evaluation mode")
    if memory_mib < 128:
        raise ValueError("address-space limit must be at least 128 MiB")
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    logs.mkdir()
    report: dict[str, Any] = {
        "scope": "arena-small-tarball-only", "full_corpus_verified": False,
        "archive_sha256": sha256_file(archive), "binary_sha256": sha256_file(binary),
        "modes": modes, "timeout_seconds": timeout, "address_space_limit_mib": memory_mib,
        "removed_environment_variables": sorted(k for k in os.environ if k.startswith("KIOTA_")),
        "results": [], "passed": False, "complete": False, "running": None,
    }
    write_report(output, report)
    try:
        with tempfile.TemporaryDirectory(prefix="kiota-arena-") as tmp:
            cases = unpack_cases(archive, Path(tmp))
            good = sum(expected == 0 for _, expected, _ in cases)
            bad = len(cases) - good
            report["counts"] = {"good": good, "bad": bad, "total": len(cases)}
            if good < min_good or bad < min_bad:
                raise ValueError(f"incomplete suite: {good} good / {bad} bad; "
                                 f"minimum {min_good} / {min_bad}")
            for mode in modes:
                for ordinal, case in enumerate(cases):
                    report["running"] = {"mode": mode, "test": case[0]}
                    write_report(output, report)
                    print(f"RUN {mode} {ordinal + 1}/{len(cases)} {case[0]}", flush=True)
                    result = run_case(binary, case, mode, timeout, logs, ordinal, memory_mib)
                    report["results"].append(result)
                    report["running"] = None
                    write_report(output, report)
                    status = "PASS" if result["passed"] else "FAIL"
                    print(f"{status} {mode} {result['test']}: {result['outcome']} "
                          f"{result['wall_seconds']}s", flush=True)
                    if not result["passed"]:
                        print(result.get("diagnostic_tail", ""), flush=True)
            report["complete"] = True
            report["passed"] = all(result["passed"] for result in report["results"])
    except (OSError, ValueError, tarfile.TarError) as exc:
        report["error"] = str(exc)
    finally:
        write_report(output, report)
    return report


def main() -> int:
    if len(sys.argv) == 6 and sys.argv[1] == "--exec-limited":
        try:
            exec_limited(int(sys.argv[2]), sys.argv[3], sys.argv[4])
        except (OSError, ValueError) as exc:
            print(f"child setup failed: {exc}", file=sys.stderr)
        return 3
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mode", choices=("default", "nbe", "both"), default="both")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--memory-mib", type=int, default=4096)
    parser.add_argument("--min-good", type=int, default=119)
    parser.add_argument("--min-bad", type=int, default=70)
    args = parser.parse_args()
    modes = ["default", "nbe"] if args.mode == "both" else [args.mode]
    try:
        report = run_gate(args.binary, args.archive, args.output, modes, args.timeout,
                          args.min_good, args.min_bad, args.memory_mib)
    except (OSError, ValueError) as exc:
        parser.exit(2, f"arena gate setup failed: {exc}\n")
    counts = report.get("counts", {})
    failures = sum(not item["passed"] for item in report["results"])
    print(json.dumps({"passed": report["passed"], "complete": report["complete"], "counts": counts,
                      "executions": len(report["results"]), "failures": failures,
                      "error": report.get("error"), "scope": report["scope"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
