---
status: ready
priority: p1
issue_id: "005"
tags: [kernel, rank-one, soundness, remote, performance]
dependencies: ["001", "002", "004"]
---

# Achieve verified rank one on the official Lean Kernel Arena

## Problem Statement

The user explicitly requested rank one and continued remote execution. Kiota is
currently twentieth, with one Mathlib false rejection, six valid declines, and
no Mathlib instruction score. Passing unit tests or changing the board's field
size does not meet this goal.

## Findings

September30 live readback: position20/25 (previous20/27), 71 invalid rejected,
124 valid accepted, one false rejection and six declines. Official pin:
2d2a9fa31cba31abdd49543c3bb667591207577e.
Current leader mathgraph accepts Mathlib at776598915229 instructions; this
is a moving reference, not a guaranteed target for a future round.
Official Mathlib rejects CategoryTheory.Functor.IsHomLift's large elimination.
Diagnostic source already replaces intern-pointer comparison of conclusion
BVars with numeric indices and includes reset-state positive/negative controls.
That correction has not been verified on full current Mathlib.

Remote Init's prior Docker startup blocker is fixed at5f3160c, with32 policy/
supervisor tests and197 Rust tests passing. Exact Init then actually rejects at
declaration17726, Int32.instRxcHasSize_eq, in127s, without OOM or timeout.
Projection trace source d3b6c55 is pinned by orchestration8704fcc; run36716037326
is the next bounded diagnostic, not an acceptance.

## Proposed Solutions

1. Correctness-first staged optimization: fix smallest real kernel failure,
   preserve typed negative controls, then profile memory and instruction hotpaths.
   Higher effort but measurable and avoids faster unsound acceptance.
2. Promote small-suite fixes immediately: simpler deployment, but fails the
   required full-corpus, resource and soundness evidence gates. Not selected.
3. Raise resource limits or skip hard inputs: masks failures and does not prove
   rank-one capability. Not selected.

## Recommended Action

Use remote GitHub runners for source, tests, corpus generation and artifact
storage. Serialize shared checker edits. Preserve fixed input hashes, immutable
checker/orchestration SHAs and unchanged limits in each diagnostic. Lightweight
local API coordination only; no local checkout edits, compilation, exports or
checker runs. Do not merge or alter the official Arena pin until candidate gates
and review succeed. No paid compute or Kaggle submission without fresh authority.

## Acceptance Criteria

- [x] Rank-one objective and remote-only operating constraints recorded.
- [x] Current official pin, verdicts and leader instruction baseline read back.
- [ ] Remaining shortcut audit and targeted adversarial regressions complete.
- [ ] All193 downloadable cases pass strict unchanged resource gate.
- [ ] Exact current Init and Std accept, with input/source/binary provenance.
- [ ] Current Mathlib false rejection eliminated with reduced positive/negative controls.
- [ ] Exact full Mathlib accepts; other valid false rejects/declines resolved.
- [ ] Competitive full-Mathlib Linux instruction metric measured reproducibly.
- [ ] Independently reviewed exact-head CI and immutable candidate gates pass.
- [ ] Verified candidate is pushed/promoted and official Arena pin updated.
- [ ] Official live board reads back Kiota at position1 with expected revision
      and soundness/correctness counts and a finite Mathlib instruction score.

## Work Log

### 2026-09-30 - Goal resumed and first remote blocker closed

Remote commits5f3160c,d3b6c55,8704fcc isolate the Docker-policy fix from checker
diagnostics. Pipeline retains the 6GiB/no-swap/600s constraint and bounded logs,
never full exports. Init generation and checker execution are distinct evidence.
Normal CI succeeds; strict memory gate remains separate and incomplete.
Official pin/score unchanged. No local file was edited or heavy task executed.

## Resources

- https://arena.lean-lang.org/
- https://github.com/sankalpsthakur/kiota/actions/runs/36715157362
- https://github.com/sankalpsthakur/kiota/actions/runs/36716037326
- https://github.com/sankalpsthakur/kiota/pull/12
