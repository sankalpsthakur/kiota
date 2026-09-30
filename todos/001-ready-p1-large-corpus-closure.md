---
status: ready
priority: p1
issue_id: "001"
tags: [kernel, correctness, performance]
dependencies: []
---

# Complete large-corpus checking

## Problem Statement

The live checker rejects Mathlib/CSLib, declines Init, and cannot complete
Std/Cedar. Current main contains Prop-elimination fixes absent from the arena.

## Findings

- Candidate baseline: 9fa2c29; live arena: 2d2a9fa.
- Release suite passes 83 library and 70 export tests on 2026-09-27.
- Exact 6 MB Int32 slice declines at WHNF depth limit in 2.03 seconds.
- Diagnostic trace expands symbolic Nat.add into Nat.rec on a bound near 2^31.
- The CLI retains the entire raw export beside its parsed environment.
- Local disk headroom was 11 GB at the initial checkpoint; latest check is
  4.4 GiB. Do not download/build full Mathlib locally; large checks must run
  remotely, serially, and bounded.

## Proposed Solutions

1. Stream CLI input: small, independently measurable memory improvement.
2. Correct lazy arithmetic/conversion behavior: larger semantic change requiring
   adversarial replay and exact slice acceptance.
3. Raise depth limits: does not address billions of recursive reductions; avoid.

## Recommended Action

Verify streaming separately, then diagnose symbolic arithmetic using the exact
slice. Preserve negative tests and record candidate/baseline binary hashes.

## Acceptance Criteria

- [x] File and stdin parsing preserve acceptance/rejection behavior.
- [x] Current downloaded arena corpus has no false accepts or new false rejects.
- [ ] Exact Int32 slice accepts with bounded time and memory.
- [ ] Current candidate clears Mathlib/CSLib Prop-elimination failures.
- [ ] Full Init, Std, Cedar, Mathlib, and CSLib accept on one candidate.
- [ ] Arena pin and live benchmark match the verified candidate.

## Work Log

### 2026-09-27

Reproduced baseline Int32 decline and ran release tests. Implemented input
streaming and verified 83 library, 70 export, and 2 CLI tests. Current downloaded
corpus passes 122/122 good and 71/71 bad at 90 seconds per case.
Init physical footprint: 1,064,977,704 -> 754,107,352 bytes, with the same
Int32 decline. Open-addition folding experiments did not clear the exact slice
and were removed. Experimental NbE was terminated after 42 seconds of growth.
The long magma test accepts in separate baseline and streaming runs; its initial
45-second timeout under competing jobs was not reproduced in the final replay.
Discovered unmerged PRs #10 (cache identity/error verdicts) and #11 (recursor
type reconstruction by phiferd); their changes are not on current main.

Integrated both contributions on `fix/large-corpus-20260927`, preserving author
history and reconstruction error categories. Combined default and experimental
NbE release suites pass all 180 tests; default small-corpus replay passes all
193 cases. The malformed imported recursor signature accepted by baseline is
now rejected, with its valid control accepted. Internal/parse errors return 3.
Strict memory-capped gate remains a Linux CI requirement: Darwin RLIMIT_AS
causes 8 of 16 Python harness tests to fail locally. Large-corpus criteria above
remain unchecked; no ranking improvement or end-to-end acceptance is claimed.

Linux CI passed all 16 Python harness tests and 180 default Rust release tests,
then failed the strict default gate on one allocation crash in
`magma-list-pair-n21` under 8,192 MiB address space (192/193 correct verdicts).
Added todo 002 for this separate availability blocker. Combined full Init still
declines at the same declaration: 38.41 seconds, 764,314,584-byte physical
footprint. Core-only equality normalization also failed the small Int32 slice
and was reverted; the verified binary hash was restored.

Parallel investigation refreshed the deployed truth: Kiota is 19/26 at Arena
SHA `8384b217ee3bf2da27e078af03cb647136427d57`, pinned to `2d2a9fa`.
Mathlib/CSLib still false-reject on deployed Prop recursors; Init/Con-leche
decline and Std/Cedar are availability failures. The full Mathlib accepted
instruction count is a separate ranking gate, not implied by small fixtures.

The optional head-exposure prototype still declines the exact Int32 slice
in strong mode; reclamation only prolonged its arithmetic countdown. The
prototype is preserved locally but excluded from the memory checkpoint.
No normalization/depth-limit change is presented as a fix. Existing private
Kaggle infrastructure can support serial resource checks, but the historical
runner's COMPLETE status hid declines/timeouts and is not acceptance evidence.
A strict exact-SHA replacement is being prepared; actual submission requires
the user's response. Exact Mathlib/CSLib inputs and hardware-counter access
remain separate prerequisites.

### 2026-09-30 - Corrected lazy comparison replay

Unsafe prototypef0129de exactInit36725031921 verifies current347555345byte/6487065line/SHA620502ac input and reaches declaration50862 before600stimeout/noOOM. It is not acceptance, and later strict negatives caught proj-of-subst-prop falseaccept. Do not use this run as correctness evidence. Corrected6bbc0fa adds strict projection-sort checks and passes all71 negatives in reviewed194case full matrix36727096974; onlypairRSS fails. NewexactInit is pinned to6bbc0fa with6GiB/no-swap/600s unchanged and boundedstatistics to localize remainingcost. All source/build/export/artifact work stays remote.

### 2026-09-30 - Exact Init acceptance finally verified

Run36727708589, orchestration34f6f17/checker6bbc0fa, KIOTA_LAZY_HEAD=1 andKIOTA_STATS=1: official input verified347555345bytes6487065lines/SHA620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a; all57551declarations accept, exit0,555.2989s inside unchanged6GiB/no-swap/600scontainer, noOOM. BinarySHA379038e68ad1d9377625ad5cb8a9c4d0b95151163ddb469459205e3c79a4da1d. The reported29.8MiB sampledRSS belongs to docker attach, NOT Kiota; do not claim that checker RSS. STATS41729024infer/61160876whnf/26540054defeq/604723552instnodes/707486578interncalls; totalinputscopeInit only. NoMathlib,Std,officialpin orrankclosure. Twoadditional customNeg/cast corrections are onnewsource and must separately reverify.

### 2026-09-30 - Exact Std diagnostic prepared after Init closure

Prepared remote-only Std pipeline usingcurrent official596655086bytes/10826639lines/SHA289ed65a367abdc7388a855d2acf59cc1f401f5e06295acbb8a420682d9f00bd,Lean4.34.1/exporter3.1.0,immutablechecker178c3ba. Checker runs only after fullhash/header/statistics/currentpublication comparison. Same6GiB/no-swap sandbox, **officialStd590s** timeout, networknone/read-only/boundedlogs; default100-declaration progress avoids fullStd logcap pressure without skipping declarations. Staticchecks validate bootstrap commands, scopefields, exactpin/input andcaps. NoStd run dispatched beforenewchecker normal/release/fullnegative gates readback. Mathlib remainsopen.

- Std orchestrationbcb5a94 normalCI36730016111 passes209Rust+37supervisor/staticpolicytests. Immutablechecker178c3ba alreadypasses both release modes and all71negative cases in fullmatrix36729616842 (193/194,onlypairmemory). New boundedexactStd diagnostic authorized for thisrevision, inputSHA289ed65a,6GiB/no-swap/**590s**officialtimeout. This is diagnosis, not proofStdaccepts orMathlib/rankclosure.

### 2026-09-30 - Actual Mathlib recursor slice prepared

Exact Std36730359430 remains live onimmutable178c3ba. Prepared distinct remote HomLift dependency export fromArena-pinnedMathlibd13f23b/exporter66f1fb4/Lean4.34.1; actualCategoryTheory.Functor.IsHomLift.rec andowner must be present beforechecker. Cache onlytargeted module dependencies, no fullMathlib build/export. Hash/header/source/binary readbacks andsame6GiB/no-swap with120s slice timeout. All71negative replay alreadyrejects onchecker178c3ba, but this newactualMatlib slice isnotfullMathlibclosure/rank evidence. Existing numeric-BVar large-elimination correction isnotrewritten withoutnewfailure. Corrected cosmeticStd workflowstep label; ongoingjob unchanged.

### 2026-09-30 - Exact Std OOM and actual HomLift acceptance

Std36730359430 terminal: inputverified596655086bytes10826639lines/SHA289ed65a/checker178c3ba; DockerOOMKilledtrue exit137 after568.737s insideunchanged6GiB/no-swap/590s. Actualchecker maxRSS6281448KiB fromchecker.time (dockerattach29MiB isnotcheckerRSS). Last100-declaration marker21300 Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_get_aux; it doesnotidentify exactfailingdecl. Tailcachecountswhnf19155294/core21420086/infer29350002, interncalls1.8billion. This ismemoryfailure, noacceptance.

HomLift36731974298 terminalaccept onimmutable178c3ba/orchestration7f78ec3: actualArena-pinnedMathlibd13f23b/Lean4.34.1/exporter3.1.0 selectedrecursorandall435declarationdependencies,673065bytes12080lines/SHA df2f1398d740f808c5ce0c39723822792740c5f1a682a0af07b2aa15ae202552,0.1904s,6GiB/no-swap/120sslice bound. Actualtarget/ownerpresencevalidated; nofullMathlibacceptance orrankclaim.

### 2026-09-30 - Targeted Std availability triage prepared

Preparedselected Std blastAdd.go_get_aux export withalllogicaldependencies, immutablechecker604e966 andLean4.34.1/exporter3.1.0. It islast100declmarkerofOOMStd,notprovenexactfailingdecl. Mustverifyactualtargetpresence/header/hashbeforebounded6GiB/no-swap/120schecker. FullStdremainsopen. NoMathlibcheckout/cachegatheringneededbecauseStdcomeswithLean. ExactInit/HomLiftandstrictmatrix5dd01cf remainlive; nostalerestart.

### 2026-09-30 - Exact Init cache-safe baseline and sparse-walk replay

Run36734387788 onchecker604e966/orchestration5dd01cf verifiesofficialSHA620502ac/347555345bytes/6487065lines buttimesout600.264s exit124 noOOM; lastdeclaration50930Vector.extract_push._proof_5. Earlier6bbc0faaccept555s isnotacceptanceofcache-safe604e966; correctnesscostmustbeoptimizedwithoutrestoringunsafealiases.

Sparse-set-bit-walk8094dfb normalCI36735747764 andbothrelease/fullmatrix36735968570complete194cases193pass, all71negativesreject;onlypair5GiBmemory,unchangedbounds. Reference-scanreg439 confirmsidenticalcachekeysforallmasksindepth1..10/overflow. RepinnedexactInittoimmutable8094dfbwithsameflags/input/6GiB/no-swap/600sgate. Opt-inWHNFexperimentisseparate,noeffectconfounding. NoInitacceptanceorperformancegainclaimeduntilterminalreadback.

### 2026-09-30 - Sparse Init terminal result and no-suffix follow-up

Exact Init36737090830 orchestratione59da412/checker8094dfba verifies official347555345bytes/6487065lines/SHA620502ac, timesout600.2086s exit124 noOOM at declaration55025. Baseline604e966 reached50930; increased progress is not full acceptance or hardware-independent speedup. Same6GiB/no-swap/600s, all57551 declarations required. No-suffix source08dd3a4a passes214 Rust+45 policy tests and strict matrix36737357680:194complete193pass in default/lazy-head, all71negatives reject, onlypair5GiBRSS. Repin exact Init to immutable08dd3a4a, unchangedinput/flags/limits. This source is not integrated/promoted. All work remote.
