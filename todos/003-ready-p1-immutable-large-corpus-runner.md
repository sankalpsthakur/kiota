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
- As of 2026-09-28, deployed Kiota remains `2d2a9fa`, rank 20/28: all 71
  invalid tests rejected, 124/130 valid tests accepted, one false reject and
  five declines. Candidate PR #12 is draft and not deployed. Accepted Mathlib
  hardware instructions are required for a finite ranking metric; wall time is
  not a substitute.
- The existing private `kiota-large-inputs-20260908` dataset lists Init, Std,
  and Cedar only. It contains neither Mathlib nor CSLib; Cedar is not the exact
  Arena export. Historical notebook `COMPLETE` status does not prove acceptance.

## Proposed Solutions

1. Replace the legacy runner with an exact-SHA, manifest-driven, serial harness.
2. Require corpus hash, bytes, and Lean/export format versions before checking.
3. Preserve distinct outcomes and fail the aggregate for missing/nonaccepted
   valid inputs. Retain process-group bounds and small provenance/log outputs.
4. Probe hardware instructions separately; unavailable PMU is not zero cost.

## Recommended Action

Prepare and test the harness locally with fake binaries. The user has authorized
continued progress, but submit a private full-corpus run only when the exact
inputs and source/toolchain prerequisites are available and validated. Do not
generate/build full Mathlib on the 16 GB Mac solely to fill this gap.

## Acceptance Criteria

- [x] Runner implements actual immutable-checkout and built-binary hash checks.
- [x] Tests exercise missing inputs, mismatched hashes, every exit category,
      crashes, timeouts, process-group cleanup, and incomplete execution.
- [x] User authorizes continued progress and pushing verified updates.
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

### 2026-09-28 - Live ranking and remote-input preflight

The current Arena board places Kiota 20/28 at the same official pin
`2d2a9fa31cba31abdd49543c3bb667591207577e`. It reports 71/71 negative
tests rejected, 124/130 valid accepted, one false reject, five declines, and no
Mathlib instruction score. The change from 19/26 is not a checker improvement;
the official revision did not change.

Read-only Kaggle inventory confirmed the private large-input dataset has Init,
Std, and Cedar, but no full Mathlib or CSLib. The old large-CPU notebook is
`COMPLETE`; this only indicates the notebook finished, not that all inputs
accepted. No new remote job or dataset upload was submitted. Do not promote the
draft PR or submit a mislabelled five-corpus result. A daily Codex heartbeat
now watches the rank, pin, correctness counts, Mathlib score, and PR gate and
notifies only on material changes.

## Resources

- https://github.com/sankalpsthakur/kiota/pull/12
- `docs/checkpoints/2026-09-27.md`
