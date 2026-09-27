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
- Local disk headroom is 11 GB; large checks must run sequentially and bounded.

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
