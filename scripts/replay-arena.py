#!/usr/bin/env python3
"""Replay an extracted good/bad arena corpus with a bounded per-file timeout."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("binary", type=Path)
parser.add_argument("corpus", type=Path)
parser.add_argument("--timeout", type=float, default=60)
args = parser.parse_args()
binary = args.binary.resolve()
rows = []
totals = {}
for group, expected in [("good", 0), ("bad", 1)]:
    files = sorted((args.corpus / group).rglob("*.ndjson"))
    if not files:
        raise SystemExit(f"No {group} cases in {args.corpus}")
    passed = 0
    for path in files:
        started = time.monotonic()
        try:
            result = subprocess.run([str(binary), str(path)], capture_output=True,
                                    text=True, timeout=args.timeout)
            code = result.returncode
            diagnostic = result.stderr.splitlines()[-1:]
        except subprocess.TimeoutExpired:
            code = "timeout"
            diagnostic = []
        ok = code == expected
        passed += ok
        row = {"test": str(path.relative_to(args.corpus)), "exit": code,
               "correct": ok, "seconds": round(time.monotonic() - started, 3),
               "diagnostic": diagnostic}
        rows.append(row)
        if not ok:
            print(json.dumps(row), file=sys.stderr, flush=True)
    totals[group] = {"passed": passed, "total": len(files)}
print(json.dumps({"binary": str(binary),
                  "sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
                  "totals": totals, "failures": [r for r in rows if not r["correct"]]},
                 indent=2), flush=True)
raise SystemExit(0 if all(r["correct"] for r in rows) else 1)
