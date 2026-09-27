---
status: ready
priority: p1
issue_id: "002"
tags: [kernel, performance, memory, ci]
dependencies: []
---

# Bound magma pair checking under the strict Linux memory cap

## Problem Statement

The integrated checker passes the local uncapped small corpus but fails a
published good case under the explicit Linux address-space limit. Keep PR #12
draft until this resource gate is established.

## Findings

- Candidate `6cf58c1`; Linux run 36317993571, default job 108616239752.
- 192/193 correct verdicts, including all 71 negative cases.
- `magma-list-pair-n21` crashes after 57.78 seconds under 8,192 MiB address
  space with a failed 2,281,701,392-byte allocation.
- Even the smaller `magma-list-pair-n7` accepts while building 6,264,892 live
  intern nodes and making 9,846,835 substitution-node visits locally.
- Interner resets happen between declarations; clearing it during a declaration
  without coordinating all pointer-keyed caches is not a safe shortcut.
- Whether the cap failure is inherited from baseline is not yet verified.

## Proposed Solutions

1. Compare immutable baseline and candidate on the same Linux case and cap.
2. Trace the small pair case to locate avoidable eager normalization and node
   retention, then validate a general improvement against positive/negative tests.
3. Do not raise the cap, skip the fixture, or call an allocation crash a reject.

## Recommended Action

Use bounded Linux diagnostics for the large case; do not rerun it uncapped on
the 16 GB Mac. Preserve exact inputs, binary hashes, and limits in reports.

## Acceptance Criteria

- [ ] Baseline/candidate comparison distinguishes inherited failure from regression.
- [ ] Pair-n21 accepts under the unchanged 8,192 MiB Linux address-space cap.
- [ ] Current 122 positive and 71 negative Arena cases pass the strict gate.
- [ ] Default and experimental NbE outcomes are recorded separately.

## Work Log

### 2026-09-27

Detected the strict CI crash after successful uncapped local replay. Confirmed
16 Python harness tests and 180 default release tests pass on Linux. Profiled
only the smaller pair-n7 locally; no uncapped pair-n21 rerun was launched.
Its countermodel has only 155 source DAG nodes but grows the interner from
33,993 to over six million nodes during checking, localizing the blowup to
checking that declaration rather than input parsing.

Added a conditional immutable-baseline replay to the Linux workflow. It runs
only after a failed default strict gate, uses the same archived input and
unchanged memory cap, and retains a separate report. It cannot turn the
candidate failure into a passing gate. Comparative result is pending CI.

## Resources

- https://github.com/sankalpsthakur/kiota/pull/12
- https://github.com/sankalpsthakur/kiota/actions/runs/36317993571
- `docs/checkpoints/2026-09-27.md`
