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
- Every arena suite is run. Large corpora (`init`, `std`, `mathlib`,
  `cslib`, `cedar`) are no longer declined.

## Local score (2026-08-14)

Full replay of the published arena tarball — all 178 exports, every one
run, nothing skipped. Binary built from `90ee8cf`. Measured on
macOS/arm64 without `perf`, so wall time is indicative and instruction
counts — the arena's actual ranking metric — are not measured here.

| Suite | Good (accept) | Bad (reject) | Wall |
| --- | --- | --- | --- |
| tutorial | **92/92** | **46/46** | 5.3s |
| perf | 15/16 | **2/2** | 5.8s |
| undecidability | 3/4 | — | 0.2s |
| root | **4/4** | **14/14** | 0.8s |
| **total** | **114/116** | **62/62** | **12.1s** |

Soundness is clean: **62/62 bad exports rejected, zero false accepts.**
The two good exports not accepted:

| Test | Outcome | Reason |
| --- | --- | --- |
| `perf/grind-ring-5` | reject | `Lean.Grind.Semiring.add_zero` type mismatch |
| `undecidability/subject-reduction-redex` | reject | compares the endpoints the annotation exists to avoid |

`perf/app-lam` used to time out — it did not finish in ten minutes — and
now accepts in 0.08s. It probes two separate costs, and the checker had
both: no inference cache at all (so a DAG-shared term is re-inferred per
occurrence, doubling work per level) and substitution that rebuilt
subterms it could not change. Nodes now carry a loose-bvar range so
substitution skips those subterms, and inference is memoised on
`(context id, term)`. The whole sweep went from 50.2s to 12.1s.

Outside the tarball, `nested-nonuniform-param` (`either`) rejects with
`non-uniform nested inductive parameter` in 0.01s. Large corpora are
run, not declined. Init currently rejects at
`ByteArray.utf8DecodeChar?.assemble₂._proof_1` (omega `LinearCombo`
defeq) after getting past `UInt32.toNat_shiftLeft`.

On the 2026-08-14 published tarball the ranking key was `(0
bad-not-rejected, 2 good-not-accepted, no mathlib, 5 declines)` —
**9th of 17**. That decline count is now wrong: the YAML no longer
skips those suites. Rank will move with whatever Init/mathlib actually
do when the arena runs them.

## What's missing

Ranked by what actually moves the arena key, not by effort.

1. **`Array.foldlM_toList.aux._unary`** (Init, deep). The current init
   blocker after Nat.add_assoc, Std.Iterator.step and WellFounded.fixF_eq
   all fell to theorem transparency (see below). A stuck
   `PSigma.casesOn` inside a `Nat.le` argument vs a plain successor --
   same investigation recipe applies.
2. **mathlib end-to-end.** Unknown bug count; the feedback loop is a
   sub-second init rejection, so each bug is a small experiment.
3. **Closures.** The board splits: eager implementations cluster at
   7,900-10,500 G instructions, closure-based ones at 868-2,842 G.

## Fixed this week (was on this list)

- `Nat.add_assoc` / `WellFounded.fixF_eq` / `subject-reduction-redex`:
  Lean's kernel unfolds any constant with a value, theorems included.
  kiota now does this in the cold defeq delta path (`unfold_delta`)
  and at recursor major premises (`whnf_major`) -- but not in the hot
  `whnf`, where eager theorem unfolding is a known 100x blowup.
- grind-ring-5 went 0.05s-reject -> 196s-accept -> **2.3s-accept** when
  `instantiate_core` gained a per-call (node, depth) memo: proof bodies
  are DAG-shared through the interner, and each shared occurrence was
  paying a full substitution traversal.

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
