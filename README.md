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
- Incomplete on purpose: nested inductives, full `Init`, and mathlib are
  declined until the checker can accept them honestly.

## Local score (2026-08-14)

Against the arena tarball (non-mathlib):

| Suite | Result |
| --- | --- |
| Tutorial good | **92/92** accept |
| Tutorial bad | **46/46** reject |
| Remaining completeness | `init-prelude` (`noConfusion_of_Nat.aux`), Acc matcher `step.match_1` (`n+1` vs `Nat.succ`), some perf timeouts |

Soundness on finished reject tests: no known false accepts on the tutorial
bad suite. Large corpora (`init`, `std`, `mathlib`, `cslib`, `cedar`) are
**declined**, same policy as mini.

On the arena ranking key (soundness, then completeness, then mathlib
speed) this sits with **mini / evmlean**, not with sokonanoda.

## What's missing (intentionally, for now)

- Nested and mutual inductives
- Native `Nat` / `String` kernel extensions
- Hash-consing, WHNF/defeq caches, NbE / glued values
- Parallel declaration checking
- Anything that needs `Init.Prelude` (`Fin.noConfusionType` and friends)

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

In-repo fixtures under `tests/fixtures/` (accept/reject NDJSON). Optional
full tutorial walk if `LEAN_ARENA_TESTS` points at an unpacked arena
tarball.

## License

Apache-2.0
