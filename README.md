# lkc — a from-scratch Lean 4 kernel checker (experimental)

`lkc` is an independent Lean 4 kernel type-checker written in Rust for the
[Lean Kernel Arena](https://arena.lean-lang.org/). It reads `lean4export`
NDJSON and re-checks every declaration. Exported recursor `k` flags and
iota RHS terms are **not trusted** — K-like-ness is recomputed, and iota
is implemented from first principles.

## Local ranking (2026-08-14)

Against the arena's downloadable tarball
(`lean-arena-tests.tar.gz`, 178 tests, excludes corpora > 10 MB):

| Suite | Result |
| --- | --- |
| Tutorial good | **91/92** accept (`RBTree.id_spec` still fails) |
| Tutorial bad | **46/46** reject |
| All good | **105** accept, **7** incorrect reject, **4** timeout (treated as decline) |
| All bad | **61** reject, **0** incorrect accept, **1** timeout |

Soundness on finished reject tests: **61/61**. Completeness on
non-timeout accept tests: **105/112**.

The 7 remaining completeness misses:

- `init-prelude` — `Fin.noConfusionType` (prelude still out of reach)
- `tutorial/080_RBTree.id_spec`
- `perf/beta-ladder`, `perf/grind-ring-5`
- `undecidability/alg-conv-trans-acc-{left,right}`, `subject-reduction-redex`

Large real-world corpora (`init`, `std`, `mathlib`, `cslib`, `cedar`) are
declined, same policy as `mini`.

This is a fresh implementation (not a fork of `nanoda_lib`). On the
arena's lexicographic ranking (soundness, then completeness bugs, then
mathlib speed, then declines) a 0-soundness-failure entry sits with
`mini` / `evmlean` rather than the mathlib-speed leaders.

## Building

```
cargo build --release
```

## Running

```
./target/release/lkc path/to/export.ndjson
# or
./target/release/lkc --use-stdin < export.ndjson
```

Exit codes: `0` accept, `1` reject, `2` decline, anything else = error.
