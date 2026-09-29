#!/usr/bin/env python3
"""Bounded Linux-only comparison of interner modes; no full-corpus claim."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

root = Path(__file__).resolve().parents[2]
gate = module("arena_gate", root / "scripts/arena_gate.py")
runner = module("remote_runner", root / "scripts/remote/runner.py")
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--mode", choices=("default", "reclaim", "collect"), required=True)
parser.add_argument("--archive", type=Path, required=True)
parser.add_argument("--binary", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--all", action="store_true")
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=False)
logs = args.output / "logs"
logs.mkdir()
env = runner.clean_environment("default")
env["KIOTA_STATS"] = "1"
if args.mode == "reclaim":
    env["KIOTA_RECLAIM"] = "1"
elif args.mode == "collect":
    env["KIOTA_COLLECT"] = "1"
wanted = {"good/perf/magma-list-pair-n7.ndjson", "good/perf/magma-list-pair-n21.ndjson",
          "good/perf/magma-list-deep-n21.ndjson", "good/perf/magma-list-deep-n36.ndjson"}
report = {"mode": args.mode, "scope": "arena-small-only" if args.all else "four-memory-fixtures",
          "full_corpus_verified": False, "arena_rank_verified": False, "complete": False,
          "passed": False, "address_space_mib": 8192, "rss_watchdog_mib": 5120,
          "per_case_seconds": 120, "binary_sha256": gate.sha256_file(args.binary),
          "archive_sha256": gate.sha256_file(args.archive), "results": []}
deadline = time.monotonic() + (720 if args.all else 500)
def save():
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
save()
try:
    with tempfile.TemporaryDirectory(prefix="kiota-remote-cases-") as scratch:
        cases = gate.unpack_cases(args.archive, Path(scratch))
        if args.all:
            if sum(expected == 0 for _, expected, _ in cases) != 122 or len(cases) != 193:
                raise RuntimeError("small suite changed: require explicit snapshot review")
        else:
            cases = [case for case in cases if case[0] in wanted]
            if {case[0] for case in cases} != wanted:
                raise RuntimeError("missing diagnostic fixtures")
        for ordinal, (name, expected, path) in enumerate(cases):
            print("RUN", args.mode, name, flush=True)
            command = [sys.executable, str(root / "scripts/arena_gate.py"), "--exec-limited",
                       "8192", str(args.binary.resolve()), str(path)]
            result = runner.execute(command, root, env, logs / f"{ordinal:04d}.log",
                                    120, deadline, memory_bytes=5120 * 1024 * 1024,
                                    log_bytes=8 * 1024 * 1024)
            runner.require_cleanup(result)
            result.update(test=name, input_sha256=gate.sha256_file(path),
                          expected="accept" if expected == 0 else "reject")
            result["passed"] = result["outcome"] == result["expected"]
            report["results"].append(result)
            save()
            print(json.dumps(result), flush=True)
            with (logs / result["log"]).open("rb") as stream:
                stream.seek(max(0, (logs / result["log"]).stat().st_size - 2048))
                print(stream.read().decode(errors="replace"), flush=True)
        report["complete"] = True
        report["passed"] = all(item["passed"] for item in report["results"])
except Exception as error:
    report["error"] = str(error)
finally:
    save()
print(json.dumps(report), flush=True)
raise SystemExit(0 if report["passed"] else 1)
