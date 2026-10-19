#!/usr/bin/env python3
"""Summarise a timestamped KIOTA_PROGRESS stderr log: where the time went."""
import re
import sys

path, limit = sys.argv[1], float(sys.argv[2])
marks, stats, last_t = [], [], 0.0
for line in open(path, errors="replace"):
    t, _, rest = line.partition(" ")
    try:
        last_t = float(t)
    except ValueError:
        continue
    m = re.match(r"\[decl #(\d+)\] (\S+) (.*)", rest)
    if m:
        marks.append((last_t, int(m.group(1)), m.group(2), m.group(3).strip()))
    elif rest.startswith("DECLSTATS"):
        stats.append(rest.strip()[:300])
end = max(last_t, limit) if marks else last_t
durations = []
for i, (t, n, kind, name) in enumerate(marks):
    nxt = marks[i + 1][0] if i + 1 < len(marks) else end
    durations.append((nxt - t, n, kind, name))
print(f"declarations started: {len(marks)}  log end: {last_t:.1f}s  budget: {limit:.0f}s")
if marks:
    t, n, kind, name = marks[-1]
    print(f"last started: #{n} {kind} {name} at {t:.1f}s (open {end - t:.1f}s)")
total = sum(d for d, *_ in durations)
for cut in (0.1, 1, 10, 60):
    s = sum(d for d, *_ in durations if d >= cut)
    c = sum(1 for d, *_ in durations if d >= cut)
    print(f">= {cut:>5}s: {c:6} decls, {s:8.1f}s ({100 * s / max(total, 1e-9):5.1f}%)")
print("\nslowest 60:")
for d, n, kind, name in sorted(durations, reverse=True)[:60]:
    print(f"{d:9.2f}s  #{n:<7} {kind:9} {name}")
print("\nby namespace (top 40, first two components):")
agg = {}
for d, n, kind, name in durations:
    key = ".".join(name.split(".")[:2])
    agg[key] = agg.get(key, 0.0) + d
for key, d in sorted(agg.items(), key=lambda kv: -kv[1])[:40]:
    print(f"{d:9.1f}s  {key}")
print(f"\nDECLSTATS lines: {len(stats)} (last 40)")
for s in stats[-40:]:
    print(s)
