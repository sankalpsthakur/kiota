#!/usr/bin/env python3
"""Print kiota's arena results and fail on any that is not correct.

    check_arena_results.py <arena checkout> [minimum number of results]
"""
import glob
import json
import sys

root = sys.argv[1]
minimum = int(sys.argv[2]) if len(sys.argv) > 2 else 1
counts = {}
for path in sorted(glob.glob(f"{root}/_results/kiota_*.json")):
    r = json.load(open(path, encoding="utf-8"))
    counts[r["correctness"]] = counts.get(r["correctness"], 0) + 1
    if r["correctness"] != "correct" or r.get("instructions") or r["wall_time"] > 1:
        print(f"RESULT test={r['test']} status={r['status']} correctness={r['correctness']} "
              f"wall={r['wall_time']:.2f} instructions={r.get('instructions', 0)}")
total = sum(counts.values())
print(f"RESULTS total={total} {' '.join(f'{k}={v}' for k, v in sorted(counts.items()))}")
bad = total - counts.get("correct", 0) - counts.get("either", 0)
sys.exit(0 if total >= minimum and bad == 0 else 1)
