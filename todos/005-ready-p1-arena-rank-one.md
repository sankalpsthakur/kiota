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

### 2026-10-19 - Board rebuilt (27 checkers, 234 tests); interpreters removed, Lean lazy-delta step, structure-eta types, export-node release

Board readback (run of 2026-10-15, arena 315f24d4, 27 checkers, 234 tests): kiota
is 22/27, key (0, 1, inf, 9), still on pin 2d2a9fa. On this board main pinned
scores (0, 0, inf, 9) = 16th, and removing every non-mathlib decline leaves it
16th; only mathlib acceptance moves it (15T instructions = 14th, 10T = 10th,
6T = 8th, 4T = 5th). The 11 new tests change nothing for kiota.

Landed by fast-forward, each with regression tests that fail on the previous
code, chain main = 779e804 (01f05ae → 7bde9a7 #21 → 0dbc0d8 #22 → 633283d #24 → 779e804 #23, 2026-10-19 18:40Z):
- #21: the name-matched Int, Lean.Omega, Int.Linear, Lean.Grind.CommRing and Rat
  interpreters are gone (only Init.Prelude names are arena-guaranteed; five
  tests show false Ok(true) on main). decide/ite/dite keep their shortcuts for
  the exact Prelude constants. Same-run speedup normalized by sub-10 ms
  declarations: init 3.75x, std 7.36x, cslib 3.29x.
- #22: lazy delta takes Lean's step (unfold, then whnf_core). The four omega
  declines left by #21 disappear: init all 57,551 in 153s, std all 100,225 in
  405s, navier-stokes-euler all 124,850 in 1589s, cslib 346,637 of 379,950 at
  1800s (accepted in 1309s on a faster runner), all with zero failures in
  keep-going mode.
- #24: the parser releases export nodes after their last reference (a first
  pass over the file computes last references; released slots read as errors)
  and the proofs of theorems no expression mentions. Retained memory on mathlib
  is 6.95 GB at 300k declarations against 6.85 GB at 302k without it: almost every mathlib theorem is mentioned by a later expression, so nearly every proof is kept (a lower bound with every large proof released measured 4.3 GB; swapping referenced proofs to disk is the next step). A size-based proof cut
  was rejected because kiota's delta path unfolds large theorem proofs for real
  (8 cslib and 11 mathlib declines).
- #23: Lean's type comparison before structure eta (PUnit.unit.{1} converted to
  PUnit.unit.{2} on main).

Open:
- Runaway declarations: mathlib #314513
  (AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_isAffine_of_locallyOfFiniteType:
  Spec.map (𝟙 R) vs 𝟙 (Spec R); the main path fully normalizes instance
  structures while comparing proof-field types for proof irrelevance), cedar
  Cedar.Thm.pe_duration_toMinutes, con-leche ConLeche.defeqLoop_shift. Lean
  compares fields on partially unfolded terms; the fix is a Lean-style main
  path (whnf_core, exhaustive lazy delta with structural comparison at each
  step, full whnf last).
- Mathlib on the arena needs the 3600s timeout in kiota.yaml raised to the
  test's 5680s and the runaway fixed; both are Sankalp's calls (pin PR).
- GitHub runners (16 GB) die on mathlib past ~300k declarations without #24;
  artifact downloads hit the account's egress limit on 2026-10-19 (read numbers
  from job logs).

### 2026-10-19 (evening) - The mathlib runaway was cache fragmentation; cslib accepted in full; proofs to disk

The #314513 runaway was not reduction order. Two single-declaration experiments
(full WHNF replaced by whnf_core before the structural comparison; no early
proof-irrelevance inference in the core) died exactly like the baseline, and so
did LAZY_DELTA_STEPS = 512 (run 39300825337). The cause is the cache keys: an
open term's key names the binders it uses plus their types' transitive
dependencies, but the occurrence bitset behind it is one word, so a term that
mentions a binder past index 63 keyed on the whole telescope, and the WHNF
caches keyed every open term on the whole telescope at any depth. Under 110
binders 67% of key computations fell back (`CTXKEY calls=7,262,532
fallbacks=4,838,949`, run 39307176721) and every binder pushed by a Pi/Lam
congruence or an eta expansion made all cached work on the instance terms
unreachable: whnf_core 4.8M entries for 125k distinct terms across 51k
contexts, whnf 3.0M/86k, infer 2.4M/87.5k, defeq 883k/35.7k pairs; 9 GB,
never finishing.

PR #25 `fix/context-keys-past-64-binders` (2b54a70): exact occurrence lists for
overflowed terms (sorted indices, one computation per node, `None` past 64
entries so a 4000-binder perf test keys on the whole telescope as before), the
same closure and binding-by-binding id over them, WHNF caches keyed like
inference. Tests: a Prop-vs-Type dependency padded with 64 closed binders still
cannot leak across contexts. Evidence (510a31f, the bitset version with the same
keys; the list version 2b54a70 re-ran the single declaration, 11.8 s, and the
small suite, see below):
- #314513 alone: 12.8 s (run 39307336120) against never finishing.
- init all 57,551 (184.0 s → 121.3 s), std all 100,225 (376.8 s → 267.1 s),
  cslib ALL 379,950 accepted in 1619 s against the 1800 s limit (main timed out
  at 1800 s with 379,531 started on a faster runner), zero failures everywhere, peak RSS unchanged
  (runs 39308279309). Cross-runner; the std slow tail collapsed (Int64 div/mod
  4-5 s each → under 0.7 s; DHashMap ofList_cons 3.4-3.8 s → under 0.7 s), which
  runner variance does not do. Same-runner paired timing against main, two alternating rounds (run
  39310825568): init 209.9/189.3 s → 141.3/163.3 s (−24%), std 466.7/429.2 s →
  312.7/282.5 s (−34%); on the list version 2b54a70 (run 39312829800): init
  183.6/189.1 s → 135.0/132.8 s (−28%), std 377.7/390.1 s → 260.4/259.3 s (−32%).
- Mathlib from #314514 on (run 39308451072): declarations 314,514 to 622,201 in
  about 2980 s of checking, 10.9 GB resident at 622k without the proof store,
  three declines on huge literals (Real.log_three_near_10, Real.log_five_near_10:
  the 256-bit byte cap; Batteries Char.isLower_toUpper_eq_false._proof_1_3: the
  2^29 countdown budget), no reject, then a second runaway in the same file at
  #622201 (Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_…).
- Mathlib from #622202 to the end on keys + proof store (run 39318533070, the
  harness releasing skipped declarations' proofs and resetting the interner as
  the real run does): all 73,036 remaining declarations in about 600 s, peak
  7.2 GB, two declines on the same 256-bit literal cap (Real.pi_gt_d20,
  Real.pi_lt_d20), no reject.
- Mathlib from the start on the fix (run 39308279309, keep-going, 14.5 GB cap):
  443,820 declarations in 5680 s (main: 302k at 4200 s, then the runaway), no
  reject, the same three literal declines, 9.1 GB resident at 442k without the
  proof store. Whole-corpus estimate on a GitHub runner: 3900 + 2980 + 600 ≈
  7500 s, about 4400 s on the arena machine: inside the test's 5680 s, outside
  kiota.yaml's 3600 s cap.
- The first list-free version crashed perf/app-lam and perf/shift-cascade under
  the small-suite gate's 8 GiB cap (a memo keyed on node and depth is quadratic
  on a 4000-deep lambda nest); the list version with the 64-entry cap is what
  the PR carries. Gate on 2b54a70: default mode fails only the known pair-n21 cap crash, reclaim only
  magma-list-deep-n36, nbe the same seven perf tests, all exactly as on #24.

PR #26 `fix/proof-store` (d2f67a2, stacked on #25): released theorem proofs go to an
unlinked temp file (post-order DAG, shared nodes once, hash verified on reload)
and come back on demand in `unfold_delta`; a damaged blob is an error, never a
term; a write failure keeps proofs in memory. 140 unit + 88 export tests.
Evidence on the previous base (run 39309536393): init/std zero failures both
sides, peak RSS init 2410 → 2272 MiB, std 2624 → 2405 MiB; cslib all 379,950 accepted in 1287 s at 3.5 GB peak against 1414 s at 4.95 GB
for the keys fix alone (the reload path works end to end). Mathlib from the
start (run 39309536393, keep-going, 14.5 GB cap): about 436k declarations in
5680 s, one decline (the Batteries countdown), no reject, 4.1 GB resident at
310k, 4.9 GB at 436k, 6.3 GB peak, against 9.1 GB at 442k and 9.9 GB peak
without the store.

Open:
- Landing #25 and the proof store needs Sankalp's go; then the pin PR
  (rev → new main, `timeout: 3600 → 5680`, drop `declines: cslib`) is his and
  nomeata's call.
- #622201 is the next runaway (diagnosis `remote/diag-622201`); the two Real.log
  declines are fixed on `fix/huge-literal-peel` (69c545c: one peel of a literal
  over 256 bits is allowed, a countdown of it declines after 16 consecutive
  peels; both declarations accept in a windowed run, 4.3 GB resident at 443k
  with the proof store); the Batteries countdown decline needs its own trace. cedar
  `pe_duration_toMinutes` and con-leche `defeqLoop_shift` are to be re-measured
  on the keys fix.
- Kaggle gate22/gate24 kernels stall on #314513 (no keys fix) until their
  20000 s limits; deleting them is Sankalp's call.

### 2026-10-19 (night) - Literal peel and the lazy-delta re-check landed; mathlib has no known decline left

Two follow-ups to the evening's landing close the literal declines:
- #27 (d378235): a literal over 256 bits is peeled in iota like any other
  (Lean turns a literal major into `succ (n - 1)` whatever its size); only a
  run of more than 16 consecutive peels of such literals, each one less than
  the last, declines. `Real.log_three_near_10`, `log_five_near_10`,
  `pi_gt_d20` and `pi_lt_d20` accept in windowed mathlib runs (runs 39318667454
  and 39320886792).
- #28 (c064ab6): a declaration the eager pass declines or rejects is checked
  once more with Lean's lazy delta as the main path (`whnf_core` both sides,
  unfold one definition head at a time, compare a shared head's arguments
  before unfolding it, structural comparison once at the end). The eager
  path stays the default because it is faster everywhere measured (the lazy
  loop as the main path cost 5-6% on init and std on one runner, run
  39325232410, and 17% on cslib across runners); the retry costs nothing on
  declarations the eager pass accepts. Batteries
  `Char.isLower_toUpper_eq_false._proof_1_3`, the last mathlib decline (an
  `Int.Linear` certificate whose `Nat.add x 4294967264` the eager path turned
  into a 2^32 countdown), accepts under the retry (run 39329552641, the declaration alone over #25 +
  #26 + #27: zero failures).
- Small suite in default mode under the gate's own limits, with the retry: the
  known pair-n21 cap crash only (runs 39329552641 and 39335086763); reclaim and
  NbE modes as on main.
- init/std/cslib keep-going A/B of the retry against #25 + #26 (run
  39329552641, cross-runner): init 127.3 s → 141.3 s, std 233.0 s → 262.1 s,
  cslib 1680.9 s → 1651.3 s, all accepted with zero failures; the eager path is
  unchanged, so the small corpora see runner noise only.
- Mathlib curves (from the start and from declaration 440,000, keep-going,
  14.5 GB cap): on #27 (run 39324323638), 480,045 declarations in 5680 s from the start with
  the Batteries decline as the only failure and no reject (6.1 GB peak), and
  from 440,000 to the end of the corpus in 2256 s with no failure (7.6 GB
  peak); on #28 (run 39329659992), from 440,000 to the end in 2711 s with no failure
  (7.5 GB peak) and from the start 5680 s past declaration 442,000 with no
  failure (6.1 GB peak): the whole corpus with no decline and no reject.

Pin PR: leanprover/lean-kernel-arena#277 (fork branch bump-kiota-2026-10-19):
rev c064ab6, timeout 5680, cslib decline dropped. Opened 2026-10-19 23:30Z on
Sankalp's go.

Open:
- The lazy loop as the main path (not the retry) checked 576,677 mathlib
  declarations in 5680 s with no failure against 480,045 for the eager path on
  another runner (run 39324815356 against 39324323638), at about 1.5 GB more
  resident memory; a same-runner paired comparison decides whether it should
  be the default for mathlib speed.
- kiota.yaml's 3600 s timeout and the cslib decline are addressed by the pin
  PR; on the arena machine the whole of mathlib is expected at about 4400 s.
- cedar `pe_duration_toMinutes` and con-leche `defeqLoop_shift` are the same
  countdown family and should now be re-measured on main.
- Kaggle gate26 (keys + store, whole corpus, 30 GB, no time cap short of the
  session's) was still running at 23:30Z; its number is the single-process
  full-mathlib measurement.

### 2026-10-20 - Whole-corpus confirmations after the night's landings

- Kaggle (4 CPU, 30 GB, byte-identical export), keys + proof store before
  #27 and #28: the whole of mathlib, 695,238 declarations, in one process,
  16,990 s, 7.8 GB peak, exactly the five literal declines that #27 and #28
  then removed. Kaggle runs about 2.1x slower than a GitHub runner, so this
  is consistent with the windowed estimate of about 7500 s on GitHub and
  4400 s on the arena machine.
- cedar on main (run 39342048049): all declarations accepted, zero
  failures, 452 s against the 940 s limit, 4.95 GB peak; the old
  `pe_duration_toMinutes` runaway is gone.
- con-leche on main (same run): 82 declines, all "WHNF core depth limit" on
  the BitVec-64 family (`wscopedBP`, `leavesSubP`, `instantiate1P` equation
  lemmas), 460 s, 12.8 GB peak. This family is the recursor depth cap on
  `Fin.val (2^64 ...)` terms, not the countdown family, and is unchanged.
- The same-runner mathlib timing settles the open question from the night:
  the eager main path reaches 227k-231k declarations in 2000 s where the
  lazy loop as the main path reaches 202k-207k (run 39341372877, two
  rounds), so the eager default with the lazy re-check stays.
- Small-suite gate on main 4da1c58: unchanged (pair-n21 under the 8 GiB cap
  in default mode only).
- The arena's own CI on the pin PR (lean-kernel-arena#277) built kiota at
  c064ab6 and ran the non-skipped tests: every bug, other and perf test as
  expected, including pair-n21 in 34 s uncapped; the two 60 s timeouts on
  `eta-struct-major-and-no-whnf` and `eta-struct-major-no-whnf` are the
  either-tests built to not terminate for a kernel that normalizes a
  recursor's major premise first, identical on the old pin.

Open: con-leche's BitVec depth-limit family; structure eta on a major
premise before normalizing it (the two either-tests); the pin PR's review.

### 2026-10-28 - Pin #277 merged 10-20; board 21/31 on one forged quotient; parser hardening

Board readback (arena 1a1d74fa, results of 2026-10-24 with reruns to 10-28,
31 checkers, 242 tests): the pin PR leanprover/lean-kernel-arena#277 was merged
by nomeata on 2026-10-20 06:32Z, so kiota runs at c064ab6 with the mathlib
timeout. Key (1, 0, inf, 5), 21st of 31:

- `bugs/forged-quot-ind` (new, #308) accepted: the only `bad_not_rejected`
  on the board. `handle_quot` validated the Pi count of a quotient
  declaration, not its type, so a lone `Quot.ind` over user definitions of
  `Quot` and `Quot.mk` was admitted and `try_quot` proved `True → False`.
- `bugs/loose-bvar-value` (new, #306): internal error (exit 3), scored as a
  decline, where a rejection is expected.
- mathlib: killed at 5680 s at declaration 575,600 of 622,201 (92.5%). The
  arena runner is `nscloud-ubuntu-22.04-amd64-8x16` (8 vCPU, 16 GB); on the
  tests kiota accepts it spends 1.5-2.5x the official kernel's instructions
  (cslib 2.2x, cedar 2.46x, std 1.75x, init 1.58x), so mathlib would land
  near 25-28T instructions, below every accepted checker (tenet-hs 18.0T).
  Single-threaded at 4.4-4.7 G instructions/s; every checker above 10T wall
  speed uses several cores.
- The other four new bug tests (nested-name-capture, pi-closure-context,
  closure-level-subst, unit-rec-rule) are rejected.

Ranking arithmetic on this board: with the two fixes the key is (0, 0, inf,
4) = 17th, ahead of lean4cobol (7 declines) and behind the 16 checkers that
accept mathlib. A mathlib acceptance at 25-28T is also 17th; the rank moves
only once mathlib is accepted under 18T (16th), 15.9T (15th), 14T (14th),
11.6T (12th, the official kernel), 2.7T (3rd).

Fix branch `fix/quot-canonical-types` (PR #29): quotient declarations are
compared with `add_quot`'s types over the installed `Quot`/`Quot.mk`/`Eq`
primitives; a loose bound variable in any declaration-level expression is a
rejection at the record; a spelled name is declared once and the by-name
lookups (`Nat`, `String`, `Quot`, `Eq`) resolve through the declared-name
map. Local release binary on the published small suite: every `good/*`
quotient user accepts, every `bad/bugs/*` and `bad/other/*` rejects.
