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
- [ ] Independent review validates fixture and conversion semantics.
- [ ] Release tests and strict small-suite results recorded distinctly.
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
