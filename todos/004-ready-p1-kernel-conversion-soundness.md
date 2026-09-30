---
status: ready
priority: p1
issue_id: "004"
tags: [kernel, soundness, nat, ofnat, remote]
dependencies: []
---

# Preserve Lean kernel conversion instead of mathematical identities

## Problem Statement

The 5c5351a checker conflates theorem-level Nat identities with definitional
conversion and reads an OfNat instance's numeral tag instead of its value.
Public ranking evidence and existing adversarial suites do not cover these cases.
No performance candidate may be promoted before this correctness gate.

## Findings

Remote diagnostic head 3a5a1f4, CI 36621542392: fixture body/type controls pass,
then all three negative conversion assertions fail by false acceptance:
zero-add-neutral, successor-add-neutral, and custom OfNat Nat 7 storing 42.
The latter's actual constructor projection correctly returns 42.

## Proposed Solutions

1. Remove unsupported shortcuts and fall back to checked definitions/projections.
   Low semantic risk; potential availability/performance regressions require gates.
2. Add instance-aware optimizations after exact semantic controls and oracle tests.
   Higher implementation/review effort; never assume numeral tag determines value.

## Recommended Action

Apply minimal removals remotely, independently review, test release/default and
strict downloadable inputs, then audit other Nat and class-instance shortcuts.
Do not merge the diagnostic branch or change the official pin based on unit tests.

## Acceptance Criteria

- [x] Typed regressions reproduce actual false conversions on the prior source.
- [x] Minimal three-case fix passes normal exact-head Linux CI (195 Rust tests).
- [x] Independent review validates fixture and conversion semantics.
- [x] Release tests and strict small-suite results recorded distinctly.
- [ ] Remaining symbolic arithmetic and instance-blind shortcuts audited/covered.
- [ ] Full exact-corpus acceptance and live rank recorded separately.

## Work Log

### 2026-09-29 - Remote-only regression and minimal correction

Socrates supplied static analysis grounded in Lean v4.29 kernel/Prelude semantics.
Initial d7f5c7c setup hit pending-declaration self guards, not a conversion verdict.
3a5a1f4 validates bodies/types outside that guard and exposes three false accepts.
894fa49 removes Nat.add's left-zero and left-successor shortcuts and the
OfNat.ofNat tag shortcut, allowing ordinary delta/projection reduction instead.
CI 36621768690: 104 library, 2 CLI, 4 mode, and 85 export tests pass (195 total).
No local build, test, download, source edit, or checker process was launched.
Separate strict downloadable gate pending. Remaining Int/Rat OfNat recognition
and Nat.mul symbolic reductions require targeted review; not a global soundness claim.

## Resources

- https://github.com/sankalpsthakur/kiota/commit/894fa49aa1f8fa9ce16afda8af7a3198a3f507fc
- https://github.com/sankalpsthakur/kiota/actions/runs/36621542392
- https://github.com/sankalpsthakur/kiota/actions/runs/36621768690

### 2026-09-30 - Broader instance controls and strict resource result

Independent Hegel review validated the original typed fixtures and minimal
removals. Additional typed custom Add Nat and Int OfNat regressions reproduce
two more bugs at c98a478 (CI 36622947772): the custom Add projects 42 but
instance-blind substitution gives 49; the raw Int recognizer reads tag 7 instead
of field 42. 20ef776 removes class-method-to-primitive substitutions and lets
closed Int recognition conservatively decline an unreduced OfNat accessor.
65a1c7b adds positive custom Add conversion to 42, so a merely stuck accessor
cannot pass. Exact-head normal Linux CI 36623326107 succeeds: 197 Rust tests.
This is a diagnostic pushed branch, not production or official-pin promotion.

Release/full downloadable run 36622139501 at f80e323 completes 192/193,
with 195 Rust tests and 29 remote-runner tests passing. All 71 negative cases
reject. Only pair-n21 fails the stronger 5GiB RSS watchdog in 17.276s; the
8GiB address-space limit and 120s per-case limit were unchanged. Later-head
strict results remain distinct and pending; do not copy this verdict onto them.

Batch collector run 36621274996 at 2058ec2 failed all three kernel memo caps:
50k/200k/1M each times out on deep-n36 at 120s. No collection promotion.
Remaining symbolic Nat.mul/sub, Int/Rat numeral/cast and other class-instance
recognition paths still require audit/regressions. No global soundness claim.

Official readback on September 29 UTC: Kiota remains position 20, now among
27 checkers; 71 invalid rejected, 124 valid accepted, 1 false reject, 6 declines,
no Mathlib instruction metric. The board now has 131 valid cases, including
con-leche. Official pin remains 2d2a9fa31cba31abdd49543c3bb667591207577e.
No rank gain is attributed to these pushed diagnostic corrections.

### 2026-09-30 - Latest strict readback and exact Init preparation

Latest exact-head small gate 36623616614 at 72f7fde completes 192/193:
all 71 negatives reject; all other 121 positives accept. Only pair-n21 hits
the added 5GiB RSS watchdog after 17.964s. Source's normal and release Rust
suites pass 197 tests. No newly introduced false verdict appears in this small
snapshot; the resource gate still fails and remaining shortcut audits stay open.

Prepared remote-only Init regeneration targeting the pinned official 347,555,345
bytes / 6,487,065 lines / SHA-256 620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a.
Lean 4.34.1, exporter66f1fb4, arena cdb3497, immutable checker72f7fde.
Checker runs only after byte/header/generated-stat/current-publication matches.
Build/generation phases use bounded logs and 12GiB RSS supervision, not file-size
limits; checker uses a separate 6GiB no-swap container and 600s timeout.
No paid infrastructure, full-export upload, local build, or local download.
Dispatch awaits final supervisor review. This is Init diagnosis, not Mathlib
acceptance or an Arena instruction measurement.

### 2026-09-30 - Exact Init dispatched after supervision review

Hegel found no blocking issue in the final supervisor and independently matched
live official Init metadata and the installer checksum. Dispatched run
36625008017, orchestration head5bc99ce, immutable checker72f7fde. Initial state
queued. It must pass remote Python compilation and the 29 supervisor tests,
resource preflight, source/input/header/publication checks, then bounded Init.
Do not call queued work completed, generation an acceptance, or Init a Mathlib
score. Current live Arena pin and ranking remain distinct. All completed agents
were closed; no local checker/build or new workspace file was created.

- https://github.com/sankalpsthakur/kiota/actions/runs/36625008017

### 2026-09-30 - Rank-one goal resumed; infrastructure failure isolated

Active objective: verified number one on the official Arena, not a local timing
or unit-test claim. All source changes, builds, exports, runs and evidence remain
remote. Current live position is 20 of 25 checkers (field shrank from 27), with
71 invalid rejected, 124 valid accepted, 1 false reject, 6 declines and no Mathlib
score. Official pin remains 2d2a9fa. Draft PR12 is unpromoted.

Init run36625008017 produced exactly the required bytes/lines/SHA and built
immutable checker72f7fde, but Docker never started the container: local logging
compression defaults on and cannot use max-file=1. Explicit compress=false
preserves the 1MiB single-file cap; new static regression controls cover logging,
unchanged 6GiB no-swap/600s bounds and explicit not-run versus checker verdict.
Remote CI and a new exact Init run must validate the repair before closure.

Next gates: exact Init diagnostic; fix smallest false reject; paired-proof memory
closure; exact Std/Mathlib acceptance; official Linux instruction measurement;
reviewed promotion and official pin; live-board number-one readback. Remaining
shortcut audits and all negative gates stay mandatory throughout optimization.
