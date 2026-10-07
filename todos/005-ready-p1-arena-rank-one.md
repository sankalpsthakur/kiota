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

Remote Init startup is repaired. A reproduced iota bug swallowed a depth
decline and returned an unapplied minor; checker55ae14b propagates the error.
Exact Init run36718955002 now correctly declines at declaration17726
(Int32.instRxcHasSize_eq) in114.85s, no OOM; it still does not accept Init.
Stuck-projection fix f4a3741 preserves the original major when reduction fails.
Checker3260d92 passes199 Rust tests plus33 supervisor/policy tests. Reviewed
strict run36720166680 executes194 unique cases:193 pass, all71 negatives
reject, and new proj-stuck-struct accepts in0.068s. Only magma-list-pair-n21
hits the unchanged5GiB RSS watchdog. No full-Mathlib or rank gain established.

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
- [ ] All194 reviewed downloadable cases pass strict unchanged resource gate.
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

### 2026-09-30 - Two reproduced checker bugs fixed, no promotion

Iota error propagation and stuck-projection head preservation each have typed
regressions reproduced on the old code and passing on the fix. Strict small
snapshot now pins SHA549477be6e17e6fc32b1c744822bfb2580be1faa10bdfc76d5154d18a3c7934e
(194cases; all193 prior hashes unchanged). Exact Init next replays immutable
checker3260d92 with the original6GiB/no-swap/600s gate. Official pin2d2a9fa
remains unchanged; rank-one goal stays active and all full-corpus gates open.

### 2026-09-30 - Current rank-one ledger and rejected experiment

Official board and raw publication4c30c4ac agree on position20/25, now125validaccepts (new proj-stuck-struct),71invalidrejects,oneMathlibfalse rejection,sixvaliddeclines; pin2d2a9fa unchanged. This extra accepted new input is not a rank gain. Leader now sokonanoda acceptsMathlib at753587633924 instructions; mathgraph776338011558. No candidate fullMathlib acceptance. Rank-one objective stays active.

Remote arithmetic fixes pass204 Rust tests; latest abort guard206+33. Lazy-head full matrix reveals an actual false acceptance (proj-of-subst-prop); default remains safe on71negatives but193/194 duepair5GiBRSS. ExactInit opt-in timesout600s. Strict projection sort validation is the next diagnostic, not a promoted fix. Retention-only also remains unpromoted (deep-n36timeout). Do not change official pin/draftPR or relaxcaps.

- Strict projection safety fix6bbc0fa closes the lazy-head falseaccept: all71negatives reject in default and opt-in runs36727096974, each193/194 (onlypairmemory).207Rust+33supervisor tests pass. New bounded exactInit replay will use immutable6bbc0fa; no official promotion, fullMathlib score, or rank gain.

- ExactInitrun36727708589 verifies57551declarations accepted on immutable6bbc0fa withlazy-head+stats,555.3sunder6GiB/no-swap/600s. First real fullInitacceptance in this remote sequence. NoStd/Mathlibacceptance, officialpromotion, orrankgain. Currentnewsourcecorrects twoadditional reproducedIntinstancebugs and needsitsown exacthead/fullcorpusgates; do notcopy6bbc0faacceptanceontoit.

### 2026-09-30 - Full Std memory gate and newly reproduced soundness gate

FullStd178c3ba isnotaccepted: exactinputmatchesbut6GiB OOM at568.7s. ActualIsHomLift recursor dependency slice435declarations accepts0.19s; notfullMathlibproof. Sparse-contextcachecounterexample reproducedonisolatedbaadfdc (coldreject/warmfalseaccept) andfix5982cb1 isunderCI, notpromoted. PriorInitacceptance6bbc0fa remainsrevision-scoped; newlyfound cache issue meansallcandidate acceptanceevidence needsrevalidationaftercorrection. Officialpin2d2a9fa remainsunchanged;rank-onegateopen.

### 2026-10-07 - Board recount, 4.34.1 corpora, four fixes landed; mathlib 219k declarations without a decline

Board readback (run of 2026-10-03, arena b1d6e91d, 25 checkers, 223 tests), recounted
with upstream master's `compute_checker_stats`, where `declined`, `error` and
`timeout` all count as declines: kiota is 20/25, key (0, 1, inf, 7). Its only
rank-costing miss is the mathlib false reject on the live pin 2d2a9fa (IsHomLift,
1957.7s). Official pin unchanged.

Corpora: all seven large tests were rebuilt with the arena's lka.py recipe and
checked against the board's sha256. init, std, cslib, mathlib (run 37534509955),
con-leche and navier-stokes-euler (run 37567635092) are byte-identical; cedar
differs by 4 lines (the only source build). The exact init export also reproduces
byte-identically on a Kaggle CPU kernel.

Landed by fast-forward, each with a negative regression test; main = ba9f61b.
- #16 5b9e917: string-literal projections reduce only when the representation
  type-checks.
- #17 512adbd: a decline inside speculative congruence retries the main path at
  the outermost frame and is re-raised unless the main path proves equality.
  perf/proj-lazy-struct now accepts.
- #19 e8152e7, 56b56ea: `succ` of an open term is left unnormalized (Lean's
  `reduce_nat` bails on free variables) and is compared with a literal by
  predecessors (Lean's `is_def_eq_offset`). The unused `fuel_nat_peels` now bounds
  a countdown from a literal of at least 2^29 (65536 peels), so it declines instead
  of exhausting memory.
- #20 ba9f61b: a bounded Lean-style lazy delta in the speculative pass steps only
  the side whose head is higher before anything is normalized.

Evidence for the landed head: cargo test 217 pass; the strict small suite matches
main in default/reclaim/nbe (all 71 negatives reject; 124/125 accept under the gate's
8 GiB address-space cap, and uncapped pair-n21 accepts at 7.8 GiB RSS, deep-n36 at
4.4 GiB). Large tests on main are all declines with no false reject: init (Int32,
~120s), std (timeout 590s), cslib (timeout 1800s), con-leche (core depth, 23.5s),
navier-stokes-euler (timeout 2400s, 9.6 GB), cedar (exhausts a 16 GB runner),
mathlib (timeout 5680s). Main would score (0, 0, inf, 7) if pinned.

Mathlib progression on GitHub runners: 2d2a9fa false-rejects at about #174k;
604e966 declines at Batteries `Char.all._proof_1` (~4000s; `c + 57345` vs
`c + 57344 + 1` counted down through the `Nat.succ` arm); #19 passes it and runs
205,184 declarations, then a 15 GB runaway in `Char.exists_eq_false_of_all_eq_false`
(`Char.all p` against its own body, normalized as `Nat.all` over 55296 values);
ba9f61b starts 219,556 declarations in 5680s at 8.2 GB with no decline or reject.
Std with lazy delta: 16,504 declarations in 590s against 14,524 before, 10-23%
faster per 1000-declaration bucket.

Diagnostics that made this fast: lean4export `-- <decl>` from mathlib's own
workspace exports one declaration's cone (9-10 MB; reproduces in 3-38s), and the
diagnostic branch `diag/node-alarm` dumps the active comparisons once the interner
passes N nodes, for runaways that never hit a depth limit.

Open:
- #18 draft (lazy-head fallback when an outermost comparison would decline), on
  top of #20: passes Init's `Int32.instRxcHasSize_eq` and reaches declaration 35,280
  of 57,551 in 500s on a Kaggle CPU with no decline; GitHub init/std run pending.
- Speed: mathlib needs several times the current throughput to finish inside 5680s
  (about 40 declarations/s). A sampling profile of std puts 38% of the time in
  `expr::intern` hash probing and ~9% in per-call `instantiate` memo churn;
  perf/reuse-instantiate-memo is in a throughput A/B. Mathlib time concentrates in
  Init/Std internals (`Std.DHashMap` alone 552s of 5109s).
- Pin bump: Sankalp's decision; no upstream PR has been opened.
- GitHub Actions throttled this account for long stretches (02:15-03:30Z and from
  ~10:00Z, 1-3 concurrent jobs); Kaggle CPU kernels with public inputs covered the
  gates.
