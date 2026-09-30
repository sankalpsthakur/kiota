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
- Linux run 36318438401 confirms the same cap failure on immutable baseline
  `9fa2c29` and integrated candidate `d8b34c1`; it is inherited.

## Proposed Solutions

1. Compare immutable baseline and candidate on the same Linux case and cap.
2. Trace the small pair case to locate avoidable eager normalization and node
   retention, then validate a general improvement against positive/negative tests.
3. Do not raise the cap, skip the fixture, or call an allocation crash a reject.

## Recommended Action

Use bounded Linux diagnostics for the large case; do not rerun it uncapped on
the 16 GB Mac. Preserve exact inputs, binary hashes, and limits in reports.

## Acceptance Criteria

- [x] Baseline/candidate comparison distinguishes inherited failure from regression.
- [x] Pair-n21 accepts under the unchanged 8,192 MiB Linux address-space cap.
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

The comparison completed in run 36318438401. Default candidate and baseline
both crash on pair-n21 under the unchanged 8,192 MiB cap: 61.53 and 59.82
seconds respectively, with the same failed allocation size. The experimental
NbE run separately has seven availability failures and is incomplete after its
step timeout; it is not a substitute for default-mode acceptance.

Implemented opt-in `KIOTA_RECLAIM=1`: weak lookup ownership, non-recycled
allocation IDs for persistent expression/context keys, and eviction of
disposable memo results at 50,000 entries. Universe identity tables are not
cleared mid-traversal. Reviewed lifetime tests cover stale inference/WHNF/defeq
and iota keys, recursive eviction, InferOnly validation, parent/child ownership,
collisions, and deep teardown. All 192 Rust tests pass both with and without
reclamation locally. A bounded local replay before the last boundary tests
passed 122/122 positive and 71/71 negative cases; pair-n21 accepted in 16.49
seconds with observed peak RSS 417,232 KiB. These are Mac measurements, not
proof of passing Linux RLIMIT_AS or an Arena instruction-count improvement.
An explicit third Linux CI mode now applies the unchanged strict gate to
reclamation. It remains off by default pending those results.

Final production-binary replay, with the failed arithmetic prototype excluded,
again passes all 193 fixtures: 102.94 seconds, observed peak group RSS
628,368 KiB under the same watchdog. The review's two test-isolation warnings
were addressed by holding other substitution-key components and the queried
expression fixed across reconstruction; only the relevant source/context
allocation identity now distinguishes the retained stale entries.

Linux run 36330794589, candidate `4bdf088`: the explicit reclaim gate is
complete but fails 192/193. Pair-n21 accepts in 34.76 seconds under unchanged
8,192 MiB address space; deep-n36 instead times out at 120.00 seconds with
over 500 million intern calls. All 71 negative cases reject. This trades one
availability failure for another, so no promotion or all-green claim follows.
Testing larger disposable memo retention (200,000 instead of 50,000 entries)
under bounded local runs; limits and expected verdicts remain unchanged.

Completed bounded experiments: larger memos, recent-root retention,
constant-time weak entry counts, and pressure-triggered conversion did not
clear the availability frontier. The 8M pressure variant hit the local
90-second watchdog on deep-n36. Restored all checker source and tests exactly
to `4bdf088`, retaining diagnostic results in the checkpoint. The opt-in mode
is not promoted, and the full strict Linux acceptance criterion stays unchecked.

## Resources

- https://github.com/sankalpsthakur/kiota/pull/12
- https://github.com/sankalpsthakur/kiota/actions/runs/36317993571
- `docs/checkpoints/2026-09-27.md`

### 2026-09-30 - Closure evaluator rejected by current remote evidence

Separate29f2e57/source6bbc0fa run36728328775 passes207 default/opt-in release tests+33harness controls, but strict corpus stops at98/194 when720stotal watchdog expires:87passes,11failures. All71negatives ran:70reject,refute-cheap-last hits5GiBRSS (not a wrong accept, not a reject). Paired-n21 remains5GiBmemorylimit17.90s; deep-n21/deep-n36 each120stimeout,27MiBRSS. Multiple foldedconstant/arg/grind cases also memory/timefail. Remaining96cases unexecuted. No closure-evaluator promotion or speed gain; don't repeat unchanged mode or raisecaps. Default/lazy-head178c3ba still193/194 withall71negativesreject and onlypairmemory.

### 2026-09-30 - Dependency-closed WHNF memo experiment

StdOOMreport has19mWHNF/21mcore/29minfer entries. CurrentWHNFmemo usesfullctx.idforanyopenterm, despitecorrectedinfer/defeqtransitiveclosure. Isolatedopt-inKIOTA_DEPENDENT_WHNF computesexactdependencyclosedctxkey (numericposition+rawtypeidentity,transitiveoutwardbindings,overflowfullid); doesnotchangekernelreductions, skipvalidation,evictmemos,orrelaxcaps. ModeimmutableperChecker. Comparelazy-headvsdep-whnf fullreviewed194caseswithall71negativesand8GiBAS/5GiBRSS/120sunchanged. Newreg438checkssharingonlyunreachablebindings,dependencydifferenceand64bitfallback. EntireRustsuitealsoexecuteswithbothflags. NofullStd/Init/rankclaimuntilboundedexactrevalidation.
