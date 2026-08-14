# kiota

An independent Lean 4 kernel, written in Rust, for the
[Lean Kernel Arena](https://arena.lean-lang.org/).
The name is **K + iota**: those two recursor knobs are recomputed,
not read from the export.

This is an **experimental** checker. It is **not** a nanoda fork and it is
**not** competitive with sokonanoda / nanoclo / official on mathlib. It
exists to be a second implementation that does not trust exported recursor
`k` flags or iota RHS terms.

If you want the world's fastest kernel, use
[sokonanoda](https://github.com/intgrah/sokonanoda). If you want a tiny
reference sketch, see [mini](https://github.com/nomeata/lean-mini-kernel).

## Thesis

- From-scratch term language, universes, WHNF, and definitional equality.
- Recursor K-like-ness is **recomputed**. Exported `k` is ignored.
- Iota is rebuilt from constructor fields, then rec-calls, in Lean's
  field-then-rec order. Exported recursor RHS is ignored.
- Nested inductives are checked, not declined: a nested occurrence must
  apply the datatype's own parameters, so `E.mk : (w : W) → L (E ⟨false⟩)
  → E w` is rejected.
- Incomplete on purpose: full `Init`, `Std`, and mathlib are out of reach
  on time and are declined.

## Local score (2026-08-14)

Full replay of the published arena tarball — all 178 exports, every one
run, nothing skipped. Binary built from the pinned rev at `343dfbc`.
Measured on macOS/arm64 without `perf`, so wall time is indicative and
instruction counts — the arena's actual ranking metric — are not measured
here at all.

| Suite | Good (accept) | Bad (reject) | Wall |
| --- | --- | --- | --- |
| tutorial | **92/92** | **46/46** | 8.5s |
| perf | 14/16 | **2/2** | 39.7s |
| undecidability | 3/4 | — | 0.3s |
| root | **4/4** | **14/14** | 1.7s |
| **total** | **113/116** | **62/62** | **50.2s** |

Soundness is clean: **62/62 bad exports rejected, zero false accepts.**
The three good exports not accepted:

| Test | Outcome | Reason |
| --- | --- | --- |
| `perf/app-lam` | timeout | eager substitution is O(n²) here — still running at 10 min, so this is a blowup, not a tight budget |
| `perf/grind-ring-5` | reject | `Lean.Grind.Semiring.add_zero` type mismatch |
| `undecidability/subject-reduction-redex` | reject | compares the endpoints the annotation exists to avoid |

Outside the tarball, `nested-nonuniform-param` (`either`) rejects with
`non-uniform nested inductive parameter` in 0.01s. Large corpora
(`init`, `std`, `mathlib`, `cslib`, `cedar`) are declined on time.

Scored on the arena's ranking key that is `(0 bad-not-rejected,
2 good-not-accepted, no mathlib, 6 declines)` — **9th of 17**, ahead of
mini (same completeness, 20 declines) and ahead of `official-v4.28.0`
and `still-nanoda`, which process mathlib but have false accepts.
Not #1: rank 3 is mathlib instruction count, and a checker that declines
mathlib sorts below every checker that processes it.

## What's missing

Ranked by what actually moves the arena key, not by effort.

1. **Delayed substitution.** `instantiate` rebuilds the term eagerly, so
   type-inferring nested lambdas costs O(n²). `perf/app-lam` is written to
   probe exactly this ("whether this cost arises depends on the checker's
   binder representation") and is the one export that times out. The same
   change is the precondition for mathlib — the checkers at the top of the
   board describe closure-based conversion (sokonanoda, and nanoclo's
   delayed substitutions) rather than eager substitution.
2. **`grind-ring-5`, `subject-reduction-redex`** — two false rejects, the
   only gap on ranking key 2.
3. **Parallel declaration checking.** The top three all run `-j4`.
4. **Then** mathlib, where the bar is not "completes" but 868 G instructions
   (sokonanoda, with PGO and `target-cpu=native`).

## Building

```
cargo test
cargo build --release
```

```
./target/release/kiota path/to/export.ndjson
./target/release/kiota --use-stdin < export.ndjson
```

Exit codes: `0` accept, `1` reject, `2` decline.

Set `KIOTA_DEBUG=1` to print both sides of an application-type mismatch.

## Tests

`cargo test` runs the fixtures in `tests/fixtures/`.

## License

Apache-2.0
