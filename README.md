# kiota

A **from-scratch Lean 4 kernel checker in Rust**, built as an independent implementation for the [Lean Kernel Arena](https://arena.lean-lang.org/).

It deliberately does not trust two pieces of recursor metadata from exported terms: the K-like flag and iota right-hand sides. Kiota recomputes both.

> **Arena-validated snapshot (`84b2fc4`)**  
> **116/116 valid exports accepted · 62/62 invalid exports rejected · zero false accepts on the published tarball**
>
> That revision was merged into the Lean Kernel Arena in [leanprover/lean-kernel-arena#131](https://github.com/leanprover/lean-kernel-arena/pull/131). Current `main` is ahead of that snapshot.

Kiota is experimental. It is not a nanoda fork, and it is not currently competitive with sokonanoda / nanoclo / the official kernel on full-mathlib throughput. The point is a second implementation with different trust boundaries.

## Why another kernel checker?

A kernel checker is the last line between a proof-producing tool and “this theorem is actually accepted by the logic.” Independent implementations are useful because they can fail differently.

Kiota's design choices are intentionally explicit:

- **From-scratch term language, universes, WHNF and definitional equality.**
- **Recursor K-like-ness is recomputed.** Exported `k` is ignored.
- **Iota reduction is rebuilt** from constructor fields and recursive calls in Lean's field-then-rec order. Exported recursor RHS terms are ignored.
- **Nested inductives are checked rather than blanket-declined.** A nested occurrence must apply the datatype's own parameters correctly.
- **Failure is allowed to be explicit.** Unsupported large corpora can be declined rather than guessed through.

The name is **K + iota**: the two recursor knobs Kiota recomputes.

## The result that got it into the Arena

The published Lean Kernel Arena tarball contains 116 valid exports and 62 deliberately invalid exports. At `84b2fc4`, Kiota replayed the whole set and produced:

| Suite | Result |
| --- | --- |
| Valid exports | **116 / 116 accepted** |
| Invalid exports | **62 / 62 rejected** |
| False accepts | **0** |

The last two valid failures fell to three fixes:

1. **Theorem transparency.** Lean's kernel can unfold constants with values, theorems included. Kiota now does that in the cold definitional-equality delta path and at recursor major premises without eagerly unfolding theorems in the hot WHNF path.
2. **Substitution memoization.** `grind-ring-5` went from roughly **196 s → 2.3 s** after `instantiate_core` gained a per-call `(node, depth)` memo. Proof bodies are DAG-shared through the interner; repeated occurrences had been paying the same substitution traversal repeatedly.
3. **Iota context depth.** The constructor-field walk stopped deepening its context while instantiating the binder it had just peeled, fixing de Bruijn indices that were uniformly off by one.

The important claim is deliberately narrow: **the Arena snapshot rejected every bad export and accepted every good export in that published test tarball.** It is not a claim that Kiota is complete or fast enough for full mathlib.

## Current frontier

Large-corpus completion remains in progress. The integration candidate reaches
`Int32.instRxcHasSize_eq` in Init and declines at the reduction-depth limit.
The arena configuration runs the large corpora, but a configured run is not
proof of acceptance. Full Init, Std, Mathlib, CSLib, and Cedar coverage must be
verified against the exact checker revision and export version.

On the integration branch, input is streamed on the checking worker, so the raw export need not remain in
memory beside the parsed environment. See the measured verification boundaries
in [the September 27 checkpoint](docs/checkpoints/2026-09-27.md).

The performance gap also points toward a deeper architectural question. Eager implementations cluster far above closure-based kernels on full-corpus instruction counts. Kiota currently keeps an eager representation; moving more evaluation behind closures is likely the next major throughput step after correctness coverage.

## Building

```bash
cargo test
cargo build --release
```

Run an exported environment:

```bash
./target/release/kiota path/to/export.ndjson
./target/release/kiota --use-stdin < export.ndjson
```

Exit codes:

- `0` — accept
- `1` — reject
- `2` — decline
- `3` — internal or input parsing error (not a proof rejection)

Set `KIOTA_DEBUG=1` to print both sides of an application-type mismatch.

`KIOTA_RECLAIM=1` enables experimental weak interning and eviction of disposable
memo tables. It is off by default. Persistent expression keys use allocation IDs
that are never recycled; eviction does not clear universe-substitution identity
tables during recursion. This mode is tested separately in Linux CI under the
unchanged resource limits. It does not change proof rules or reduction limits,
does not bound every table, and does not yet establish large-corpus acceptance
or improved Arena instruction counts.

## What to read in the code

If you are exploring kernel implementation rather than just running the binary, the interesting paths are:

- `src/tc.rs` — type checking and definitional equality
- `src/expr.rs` — term representation / interning
- `src/nat.rs` — exact natural-number reductions
- `src/parser.rs` — exported-term ingestion
- `src/stats.rs` — checker statistics

## Related implementations

If you want the fastest kernel checker in the Arena, look at [sokonanoda](https://github.com/intgrah/sokonanoda). If you want a tiny reference sketch, see [lean-mini-kernel](https://github.com/nomeata/lean-mini-kernel).

Kiota exists in the middle: small enough to reason about, independent enough to be interesting, and increasingly complete against real Lean exports.

## License

Apache-2.0
