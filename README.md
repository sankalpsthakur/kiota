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
| Acc left/right, quot-right | accept |
| `beta-ladder` | accept |
| `init-prelude`, `grind-ring-5` | decline (`Lean.Syntax` nested) |
| `subject-reduction-redex` | reject |
| Some perf tests | timeout (`app-lam`, `shared-subterm`, `discarded-argument-match`) |

Soundness on finished reject tests: no known false accepts on the tutorial
bad suite. Large corpora (`init`, `std`, `mathlib`, `cslib`, `cedar`) are
**declined**, same policy as mini.

On the arena ranking key (soundness, then completeness, then mathlib
speed) this sits with **mini / evmlean**, not with sokonanoda. Not #1.

## What's missing (intentionally, for now)

- Nested inductives (`Array`/`List` of `I`, needed for `Init.Prelude`)
- Full native `Nat`/`String` (succ/add/mul/sub/pow/beq/ble/`dite` are in)
- NbE / glued values
- Parallel declaration checking

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
