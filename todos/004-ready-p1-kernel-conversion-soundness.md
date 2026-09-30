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

### 2026-09-30 - Runner repair verified; real Init false rejection isolated

Head5f3160c passes normal CI36715110660 including 32 supervisor/policy
tests. Exact Init run36715157362 verifies the official input and successfully
starts immutable checker72f7fde in its unchanged 6GiB/no-swap container.
After127s, declaration17726 Int32.instRxcHasSize_eq rejects: projection of
non-inductive value. No OOM, Docker startup failure or timeout occurred.
Init acceptance remains false. Diagnostic-only richer projection error records
the requested structure, value, inferred type and its WHNF; semantics unchanged.

Official Mathlib false reject is CategoryTheory.Functor.IsHomLift's large
elimination check. Official2d2a9fa compares conclusion BVars by intern pointer;
72f7fde already uses the numeric index and has reset-state regression controls.
This is a promising existing correction, not proof that full Mathlib accepts.

### 2026-09-30 - Bounded trace distinguishes the actual malformed term

Exact replay36716037326 (checker d3b6c55) again rejects at declaration17726,
after150.7s, without OOM or timeout. The PProd.0 projection is applied to a
two-argument lambda; its inferred type and WHNF are Pis, not a structure.
Do not bypass this check. Optional trace906b605 retains at most16 recent iota
reductions and prints them only at a projection error. No conversion rule was
changed. Next exact replay pins this immutable trace checker with unchanged
input, memory, swap, timeout and log budgets. Normal/release and strict small
gates remain separate from large-corpus acceptance and official rank.

### 2026-09-30 - Reproduced swallowed telescope decline and minimal correction

Trace run36717033489 shows the original billions-scale Nat.rec countdown,
not a safe closed-arithmetic shortcut opportunity. Regression d124347 reproduces
the exact error-transparency failure in Linux CI36717750876: typed constructor/
minor controls pass, but a forced WHNF limit returns Ok(unapplied minor) instead
of Decline. Fix propagates ensure_pi errors with ?, never a partial reduction.
An additional positive control checks ordinary iota's type and value. Remaining
Int32 large-number laziness and other swallowed-error sites remain open; this
correction alone does not imply full Init acceptance or any Arena gain.

- 2026-09-30: checker 55ae14b36e78bf3d625ed04b5ba299fba66c37c3 passes normal CI 36718002248. Strict run 36718002323 stopped before cases: live small-suite snapshot changed; no pass or new checker failure claimed. Exact Init replay repinned to this immutable checker, projection tracing disabled after reproduction; unchanged corpus and 6 GiB/no-swap/600s gates.

- 2026-09-30: exact Init run 36718955002, orchestration 60bb488/checker 55ae14b: exact input verified, checker started, exit 2 depth decline in 114.85s, no OOM. Iota fix removes prior wrong projection rejection; Init remains unaccepted.
- Reviewed strict snapshot 4c30c4ac / SHA549477be6e17e6fc32b1c744822bfb2580be1faa10bdfc76d5154d18a3c7934e against run36623616614: all193 existing input hashes unchanged, only added good/perf/proj-stuck-struct.ndjson (SHA b2fed80e90e956f24bcbe898ce7cfef5ae4c92d0f81daf42e0a2a3c817012f6f). New expected counts123good/71bad/194total; checksum guard added, existing caps preserved.

- Regression431 reproduced stuck-projection head loss remotely in CI36719630338: both bare/applied projections changed wrapper #0 to opaque #0, while typed and constructor positive controls passed. Minimal fix preserves original expression when projection fails, matching Lean4.34.1 type_checker.cpp; constructor and string reductions unchanged. Exact-head CI and reviewed194-case strict replay pending.

- Checker3260d92 normal CI36720166778 passes199 Rust+33 supervisor/policy tests. Strict run36720166680 records194 unique executions,193 passing:71 negatives reject,122 positives accept, only pair-n21 memory-limit at5.371GB sampled RSS. New proj-stuck-struct accepts0.068s. Full report remains remote; compact terminal summary now avoids dropped oversized GitHub log line. Exact Init repinned to3260d92; acceptance pending.

- Exact Init run36720935308 checker3260d92: exact input verified, checker starts and declines at the same Int32 theorem in96.32s, exit2/noOOM. Stuck-projection preservation did not close this blocker. Next diagnostic records at most32 active conversion comparisons at the first depth failure in each declaration; flag off by default, no reduction rule or cap change. Separate retention branch tests garbage collection without memo eviction in run36722270940.

- Regression432 CI36722967172 reproduces four unsupported symbolic conversions: zero*neutral, succ-left*neutral, zero-neutral subtraction, and simultaneous successor subtraction cancellation. All typed logical-model controls and closed/defining-equation controls pass; four nonconversion assertions fail because old code returns true. Removed left-zero/left-successor Nat.mul shortcuts and replaced Nat.sub algebraic shortcuts with its actual right-successor equation. Both-closed native arithmetic preserved; huge literal symbolic peel still bounded. Exact-head CI and strict suite pending. Reference: Lean4.34.1 Init/Prelude.lean Nat.mul and Nat.sub definitions.
- Retention-only run36722270940 completes193/194 in both default and experimental modes: default pair-n21 hits5GiB RSS, collection-only pair accepts114.09s/4.50GB but deep-n36 times out120s/1.59GB. Collection without transformation eviction still regresses deep case; not promoted.

- Arithmetic fix5b1a1cc passes204 Rust +33 supervisor tests (CI36723476779); strict run36723477009 completes193/194, all71 negativesreject, onlypair-n21 memorylimit. Init trace36722721190 identifies comparison of Nat-subtraction wrapper vs Rxc.HasSize projection at ctx2; eager WHNF enters huge recursion before exposing the common head. Opt-in KIOTA_LAZY_HEAD tries only legal beta/zeta/head-delta/constructor-projection steps and same-head congruence with bounded24-step histories; no iota, operand WHNF, new primitive equations or increasedcaps. Default remains off. Typed alias/countdown regression433 and baseline/experimental full-suite gates precede exact Init opt-in replay.

- Regression433 old-code CI36724114147 fails specifically with Err(Decline WHNF-depth), all113 other library tests pass. Opt-in alias-head exposure f0129de passes normalCI36724734783 and this positive regression. Baseline/opt-in full-suite run36724733710 remains in progress. Exact Init diagnostic repinned to immutablef0129de with KIOTA_LAZY_HEAD=1, existing6GiB/no-swap/600s and exactinput guards unchanged; no acceptance or default-promotion claim.

- Lazy-head matrix36724733710 stops before corpus runs: flag-on release regression core_depth_abort_declines_not_stuck_whnf returns Ok(true) after a prior CORE_DEPTH abort. Default release controls pass. Added sticky-abort/depth checks before speculative equality identity/cache paths and typed regression434 covering depth-only, prior-abort-only and reset positive control. Feature remains opt-in; full suite and exact Init results not established.

- Abort fix5b09fff passes206 Rust+33 supervisor tests in CI36726083958. Full matrix36726122980: default193/194, all71 negativesreject; opt-in192/194, **false acceptance of bad/bugs/proj-of-subst-prop** plus unchanged pair memorylimit. Feature remains forbidden for promotion. Source diagnosis: infer_proj used a best-effort is_prop whose inferred-sort errors collapse to false. Lean4.34.1 kernel is_prop requires ensure_sort(infer_type) (PR14807). Introduced strict, error-propagating classification only at projection security checks, with valid A:Type/a:A/P:Prop controls and stuck-sort rejection. Full negative replay mandatory; no acceptance claim.
- Exact Init opt-in run36725031921 checkerf0129de verifies official hash, starts, then times out600s without OOM. No Init acceptance or speed gain. No additional unsafe Init run dispatched.

- Projection repair6bbc0fa passes207 Rust+33 supervisor tests (CI36727097846). Full default/lazy-head matrix36727096974 completes193/194 in both modes: all71negativecasesreject, including proj-of-subst-prop (previously false accepted only by lazy-head). Both still hit5GiBRSS onpair-n21; no new false verdict in this reviewed194case snapshot. ExactInit repinned to6bbc0fa with boundedstatistics; feature stays opt-in and unpromoted.
- Earlier unsafecheckerf0129de Init timeout advanced through declaration50862 List.append_left_sublist_self._proof_1_1, beyond old17726 Int32 blocker. This is diagnostic progress only: source failed a negative gate and fullInit did notaccept. Correctedchecker must independently reproduce any advance.

- Continued static audit: closed_int_value still interprets Neg.neg, Nat.cast/NatCast, HDiv/HAdd/HSub/HMul and related class methods by carrier alone. Added two typed identity-Neg Int and constant42-NatCast Int regressions, validating accessor definitions, constructor instances, terms and actual field projections before raw recognizer/public conversion assertions. Reproduction CI pending; no new correction or full-source soundness claim yet. Separate unchanged-checker closure-evaluator readback run36728328775 is active on branchfix/remote-nbe-readback-20260930.
