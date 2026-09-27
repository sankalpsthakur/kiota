---
status: ready
priority: p1
issue_id: "003"
tags: [kernel, arena, verification, remote]
dependencies: ["001", "002"]
---

# Establish exact-SHA large-corpus and ranking evidence

## Problem Statement

Small downloadable fixtures do not include full Mathlib. Existing private
Kaggle outputs labelled COMPLETE include declines/timeouts, and an older
runner collapses all nonzero exits into rejection. Neither proves acceptance.

## Findings

- Existing large CPU runner historically supplied 31 GiB RAM and 20 GiB
  working disk. Current cgroup limits and hardware PMU availability are unknown.
- Existing dataset has Init/Std inputs matching the audited snapshot, but its
  Cedar input differs from Arena bytes. Mathlib/CSLib are not mounted there.
- The historical Mathlib export SHA-256 matches Arena:
  `ca2ec20fd063b61e71867b2975c81bd989af9f879b4886b8f08cd23c767a47bb`,
  5,636,308,621 bytes. Saved outputs contain logs, not that export.
- Latest deployed Kiota remains `2d2a9fa`, rank 19/26; candidate PR #12
  is draft and not deployed. Accepted Mathlib hardware instructions are required
  for a finite ranking metric; wall time is not a substitute.

## Proposed Solutions

1. Replace the legacy runner with an exact-SHA, manifest-driven, serial harness.
2. Require corpus hash, bytes, and Lean/export format versions before checking.
3. Preserve distinct outcomes and fail the aggregate for missing/nonaccepted
   valid inputs. Retain process-group bounds and small provenance/log outputs.
4. Probe hardware instructions separately; unavailable PMU is not zero cost.

## Recommended Action

Prepare and test the harness locally with fake binaries. Submit only after the
user authorizes use of the existing private runner and the candidate gates pass.
Do not generate/download full Mathlib on the 16 GB Mac with 4.4 GiB disk free.

## Acceptance Criteria

- [x] Runner implements actual immutable-checkout and built-binary hash checks.
- [x] Tests exercise missing inputs, mismatched hashes, every exit category,
      crashes, timeouts, process-group cleanup, and incomplete execution.
- [ ] User authorizes the private remote submission.
- [ ] Exact current large-corpus inputs are mounted and validated.
- [ ] All requested corpora accept within the published limits.
- [ ] Hardware-counter probe yields meaningful positive instruction counts.
- [ ] Arena pin and published readback match the verified candidate.

## Work Log

### 2026-09-27

Parallel read-only audit found the remote runner/version mismatch and inaccurate
aggregate success states. No remote job or dataset submission was performed.
Requested authorization and dispatched an isolated new strict harness under
`scripts/remote/`; main-thread review and lightweight tests will precede use.

Implemented and independently reviewed `scripts/remote/runner.py`, with a
deliberately incomplete manifest template and no network/submission operations.
Fresh source builds require toolchain provenance; provided binaries/existing
checkouts cannot pass the source-associated public manifest gate. Manifest-only
scope and unverified Arena/rank flags are explicit. Main tightened process
ownership with unreaped-child inspection and made cleanup failure fatal across
toolchain probes, optional perf, and simultaneous input mutation. No private
remote run or dataset upload has been performed. Exact missing inputs and
externally prepared source/toolchain bundles remain prerequisites.

Main integration: all 29 fake-binary supervisor tests pass locally in 11.77
seconds; Linux normal CI now executes them separately. The checker source was
restored exactly after failed resource experiments, and its verified release
binary hash matches the reviewed `4bdf088` checkpoint. Linux supervisor execution
and real corpus checks are separate gates, not inferred from these fake tests.

## Resources

- https://github.com/sankalpsthakur/kiota/pull/12
- `docs/checkpoints/2026-09-27.md`
