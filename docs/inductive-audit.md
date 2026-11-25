# Inductive admission audit

What kiota checks before it admits an `inductive` block, rule by rule, against
the official kernel's `src/kernel/inductive.cpp`. Line numbers are for Lean
v4.34.0 (the arena exports with 4.34.1; the fixtures in this repository say
4.29.1, whose `inductive.cpp` has no `check_uniform_ind_occs`).

## Method

Differential testing. Each probe is a small block written in a Python DSL
(`scripts/inductive-audit/`) that renders to

- a lean4export ndjson file, and
- a Lean script that hands the same declaration to the official kernel with
  `Environment.addDeclCore` and prints its verdict, the recursor's universe
  shape, `k`, `isRec`, `numNested` and the rule constructors.

kiota compares the recursors of a block with the ones it reconstructs, so a
probe with a placeholder recursor only tests what fires before
reconstruction. `probe.patch` adds a hook that prints the reconstructed
recursors; the DSL writes them back into the export. A probe that kiota
accepts is therefore accepted with nothing forged except what the probe is
about. Ground truth is Lean v4.34.0-rc2 (commit 6a10ac8); for lies that exist
only in the export (`numFields`, `isRec`, rule lists) it is the honest
declaration's values plus, where one exists, a theorem the official kernel
refuses.

150 probes (`probes.py`). On 606c3c0, 24 declarations or theorems the
official kernel refuses were accepted, and 14 exports whose only fault is a
forged `isRec`, `numFields` or rule list were accepted as written. On this
branch 23 of the 24 and all 14 are refused, and kiota agrees with the
official kernel on every probe that has an official verdict except `KL5`
(structure eta on a `Prop` major, the arena's
`corner-cases/eta-struct-major-and`, outcome `either`), which is unchanged.

## Findings on 606c3c0

All need no forged prelude. "Fixture" names are under `tests/fixtures/`.

| # | What was accepted | Official kernel | Fixture |
|---|---|---|---|
| 1 | A constructor field in a universe above the type's, unless both levels were closed numerals or the field was exactly a successor of the type's level: `T.{u,v} : Type u \| mk : Type v → T`, `T.{u} : Type u \| mk : Type u → T`, `T.{u} : Sort u \| mk : Type → T`. An `ensure_sort` failure on the field was skipped. | "universe level of type_of(arg #1) … is too big" | `ind-field-univ-{other-param,same-param,sort-param}.reject` |
| 2 | Occurrences of the declared type that are not applied to the declaration's parameters and levels as written, when reduction hides it: `(fun _ => N) (T N)`, `T ((fun x => x) α)`, `T b` for `b a : U` with `U` a unit, a bare `T` passed to `fun (f : Type → Type) => N`, nested `Lu T.{v,u}` | "invalid occurrence of datatype … being declared" (4.34) | `ind-occ-{erased-nonuniform,beta-param,unit-eta-param,nested-wrong-levels}.reject` |
| 3 | A type signature naming another type of the block (`A : Type`, `Bx : A → Type` in one block), or naming a sibling's constructor in an index | "unknown constant" | `ind-type-names-sibling.reject` |
| 4 | A constructor type naming a constructor of the block: `b : (fun _ : N => N) (g T T.a) → T` | "unknown constant" | `ind-ctor-names-own-ctor.reject` |
| 5 | Parameters that are not binders as written: a constructor type or the first type's signature wrapped in an identity redex, a first signature that is a constant unfolding to the parameter binder | "incorrect number of parameters" | `ind-ctor-type-{redex,identity-redex}.reject`, `ind-first-sig-{identity-redex,via-def}.reject` |
| 6 | `numFields = 0` exported for `S \| mk : B2 → S`. `S` became unit-like and `∀ x y : S, x = y` held by `rfl`; `true = false` follows by ordinary reasoning. | theorem refused | `ind-ctor-numfields-zero.reject` |
| 7 | `isRec = false` exported for `T \| mk : T → T`. Structure eta applied to a recursive type: `∀ x : T, x = T.mk x.1` by `rfl`. | theorem refused | `ind-isrec-false-struct-eta.reject` |
| 8 | Recursor rule lists permuted, shortened, duplicated, crossed between `A.rec` and `B.rec`, or with a wrong `nfields`. `rec_of`, `rec_owns_ctor` and `ctor_minor_index` read the list. The one consequence probed (`B2.rec t f t = f` with the rules swapped) was refused at the theorem. | the kernel generates the rules | `rec-rules-{swapped,dropped,nfields,mutual-crossed,nested-order}.reject` |
| 9 | Not an accept: a constant no declaration introduced ended as `ERROR` (exit 3), which the arena scores as an error rather than a rejection. | "unknown constant" | `{def,ind-field,ind-sig}-unknown-const.reject` |

## Rule table

`S` = `check_inductive_group_structure` and its helpers in `src/tc.rs`,
`R` = `src/tc/recursor.rs`, `P` = `src/parser.rs` `handle_inductive_block`.
"Before" is the verdict on 606c3c0 when it differs.

### Types

| Rule | Official check | kiota site | Probe / fixture | Verdict |
|---|---|---|---|---|
| Names are fresh | `check_name`, :254 | `P` `reject_if_dup` | tutorial 133–139 | agree |
| No constant or projected structure under the root `_nested` in a signature or a constructor type | `check_no_nested_aux` (lean4#14616, in 4.36) | `S` "uses the reserved prefix `_nested`" | `R18`; `ind-reserved-nested-prefix.reject`, `ind-sig-reserved-nested-prefix.reject`, `ind-reserved-nested-prefix-elsewhere.accept` | agree. Before (9bb4388): accepted |
| Universe parameters distinct | `add_decl` | `S` "duplicate universe parameter" | `L3` | agree |
| Signature is closed | `check_no_loose_bvars`, :1241 | `P` `` `type` has a loose bound variable `` | `L1`, `L2` | agree |
| Signature is well typed, in the environment before the block | `tc().check(type)`, :260 | types are installed first, so `S` `check_inductive_block_syntax` refuses a signature that names a type or constructor of the block; the rest is inferred through the reconstructed recursor (`R` `validate_reconstructed_type`) | `H1`, `H2`, `H4`, `H6`; `ind-type-names-sibling.reject` | agree. Before: `H5`, `H6` accepted |
| First type shows `numParams` binders as written | `get_params`, :1138 | `S` `check_inductive_block_syntax` "does not start with its declared parameters" | `P1b`, `P3`, `H12`; `ind-first-sig-*.reject` | agree. Before: accepted |
| Other members' parameters, and all indices, modulo `whnf` | `check_inductive_types`, :262–283 | `S` `ensure_pi` | `P1`, `P4`, `P5`, `H9`; `ind-later-sig-via-def.accept`, `ind-index-sig-via-def.accept` | agree |
| Parameters of all members convertible | "parameters of all inductive datatypes must match" | `S` "parameter telescope is inconsistent" | `M1` | agree |
| `numIndices` | counted by the kernel | `S` peels `numParams + numIndices` binders, then `ensure_sort` | `H10`, `H11` | a wrong count is refused |
| Result is a sort; mutual types in one universe | :285–292 | `S` `ensure_sort`; `R` `expanded_prop_only` "different result universe" | `C1`–`C3`, `H10` | agree (refused in reconstruction, which always runs) |
| `all` is the block | built by the kernel | `R` "group is not the inductive declaration order" | `K6`, `K7` | lies refused |

### Constructors

| Rule | Official check | kiota site | Probe / fixture | Verdict |
|---|---|---|---|---|
| A constructor belongs to the type that lists it, at its index | built by the kernel | `P` "claims inductive …", "is not …'s own constructor at index" | `K4`, `K9`, `orphan-ctor` | lies refused |
| No constructor twice | "duplicate constructor name", :462 | `S` "duplicate constructor name in inductive declaration" | `K3`; `ind-dup-ctor-in-list.reject` | agree. Before: refused later, as a metadata mismatch |
| Type is well typed with only the block's *types* added | `tc().check(t)`, :468 | `S` refuses a constructor of the block, and a projection out of a type of the block (inferring it needs the type's constructor: "unknown constant `T.mk`"); a recursor of the block is not in the environment yet; the rest through the recursor's minor premises | `H1`, `H3`, `H19`, `H20b`, `R16`, `R16b`; `ind-ctor-names-own-ctor.reject`, `ind-ctor-field-proj-{own-type,erased}.reject`, `ind-ctor-field-proj-other.accept` | agree. Before: `H19` accepted; before 9bb4388's follow-up: `R16`, `R16b` accepted |
| `numParams` binders as written, convertible to the type's | `get_params`, :1138; :472 | `S` "does not start with the inductive type's parameters", "parameter telescope does not match" | `P2`, `H18`, tutorial 050; `ind-ctor-type-identity-redex.reject` | agree. Before: `P2` accepted |
| `numFields` | `declare_constructors`, :499 | `S` "numFields does not match its type" | `K1`, `K2`, `X1`, `X6`, `H8`; `ind-ctor-numfields-zero.reject`, `ind-struct-eta.accept` | lies refused. Before: accepted |
| Field universe ≤ type's, unless the type is a proposition | `is_geq(result, field) \|\| normalizes_to_zero(result)`, :481 | `S` `level::leq_all` | `B1`–`B12`, `F11`; `ind-field-univ-*` | agree on all probes. Before: 9 of 12 accepted. See "leq_all" below |
| Result is `I params indices` as written, own type, own levels, no declared type in the indices | `is_valid_ind_app`, :381 | `S` conclusion checks; the levels are compared as written, and `check_uniform_ind_occs` sees the conclusion too | `F13`, `H13`, `H17`, `R1b`, tutorial 051–053, 056; `ind-result-level-max-uu.reject` | agree. Before the follow-up: `R1b` (`T.{max u u}`) accepted |
| Index may depend on a field | allowed | allowed | `H14`, `F3` | agree |

### Occurrences and positivity

| Rule | Official check | kiota site | Probe / fixture | Verdict |
|---|---|---|---|---|
| Every occurrence is applied to the parameters and levels, as written | `check_uniform_ind_occs`, :134 (4.34) | `S` `check_uniform_ind_occs`; `P` keeps a level that simplification would make a bare parameter (`max u u`, `imax u u`, `max 0 u`) unsimplified on a constant not declared yet, so the comparison sees the written form | `D1`–`D7`, `D10`, `E8`, `E22`, `H7`, `M3`, `R1`, `R1c`, `R5`, `R6c`; `ind-occ-*` | agree. Before: `D2`, `D4`, `D7`, `D10`, `E8`, `H7` accepted; before the follow-up: `R1`, `R1c` accepted |
| An occurrence that `whnf` removes is no occurrence for positivity | `check_positivity` starts with `whnf`, :437 | `S` `positivity_whnf` | `D8`, `D9`; `ind-occ-erased-uniform.accept`; arena `vanishing-occurrence` | agree |
| No occurrence in a binder domain of a field, also when it shows only after unfolding a definition, and also when unfolding the domain would remove it | :441 | `check_arg_positive_in` "non-positive" | `sanity_neg`, `N1`, `N3`, `N5`, tutorial 054, 057, 117; arena `positivity-whnf` | agree |
| Otherwise the field ends in a valid application of a declared type | :447 | `check_positive_spine`, `check_uniform_i` | `H16`, tutorial 118 | agree |
| Reflexive occurrences | allowed | allowed | `H15`, `E20`, `N2` | agree |
| Nested: `I Ds is`, `I` an earlier inductive, some `D` mentions the block; found as written | `is_nested_inductive_app`, :1023 | `S` `check_nested_functor` (after `whnf`), `R` `scan_nested_expr` (as written) | `E5`, `E9`, `E10`, `E12`, `E16`, `E19`, `E21`, `E23`; `ind-nested-identity-redex.accept`; arena `nested-redex-aux` | agree, same number of motives |
| Nested only after unfolding is not nested | `check_positivity` "non valid occurrence" | `R` "recursive field does not exactly match a reconstructed member specialization" | `E1`, `E4` | agree (refused in reconstruction) |
| Nested parameters hold no constructor-local variable | :1049 | `R` "parameters contain constructor-local variables" | `E2b` | agree |
| Container's own constructors positive in what they are given | positivity on the auxiliary type | `check_specialized_ctor_positive` | `E6`, `E7`, `nested-neg-functor` | agree |
| No occurrence in a container's index | `is_valid_ind_app` on the auxiliary application | "nested inductive occurrence in an index", "unsupported position" | `E3`, `E17`, `E18` | agree |

### Flags, elimination, recursors

| Rule | Official check | kiota site | Probe / fixture | Verdict |
|---|---|---|---|---|
| `isRec`: some constructor binder mentions a declared type, as written | `is_rec`, :308 | `S` `check_is_rec_flag` | `G1`–`G3`, `G6`, `G7`, `X2`, `X7`; `ind-isrec-*`; arena `vanishing-occurrence` | lies refused. Before: read as exported by `is_non_rec_structure` |
| `isReflexive`, `numNested` | `is_reflexive`, :337; nested count | not read | `G4`, `G5` | a lie is accepted and has no effect |
| Elimination into `Prop` only | `elim_only_at_universe_zero`, :522, on the block with its auxiliary types | `R` `expanded_prop_only`, `S` `elim_only_at_universe_zero` | `F1`–`F12`, `E15`, `E15b` | agree on the universe shape of every recursor |
| A recursor for a `Prop`-only type that claims large elimination | n/a | `R` "Prop-only recursor has the wrong universe-parameter shape" | `large-elim-prop-bool`, `prop-subsingleton-elim-data-field`, arena `large-elim-param` | refused |
| K | `init_K_target`, :594 | `is_k_like`; exported `k` not read on this branch | `KL1`–`KL7`, `J8` | agree; a `k` lie alone has no effect (snd/export-names compares it) |
| Structure-likeness | `is_non_rec_structure`, :28 | `is_non_rec_structure` on the checked `isRec`, `numIndices`, constructor list | `X1`, `X2`, `X6`, `X7` | agree once the inputs are checked |
| Recursor names, count, type, counts | generated | `P` name and metadata comparison, `R` `validate_reconstructed_type` | `K11`, `inflated-numNested`, `extra-rec*`, `recursor-type-reconstruction` | forgeries refused |
| Rules: one per constructor of the member, in order, with its field count | `mk_rec_rules`, :748; restored names, :1281 | `P` "rules do not match its constructors" against `R` `DerivedRecursor::rules` | `J1`–`J7`, `J9`, `J10`, `X3`, `X4`; `rec-rules-*` | lies refused. Before: stored as exported |
| Rule right-hand sides | generated | not read; iota is derived from the constructor types | arena `nat-rec-rules`, `rec-rule-wrong-arg` | refused at the first use |

## leq_all

The official test is `is_geq` on normal forms, which is sound and not
complete. `level::leq_all` decides `field ≤ result` exactly: for each choice
of which parameters are zero, `imax` is `max` or `0` and both sides are
maxima of constants and `p + k`. So it admits whatever `is_geq` admits and
cannot refuse a genuine export for this reason; a declaration that only an
exact comparison admits would be accepted here and refused by Lean, and none
was found. It is checked against evaluation on 20,000 random level pairs
(`level::tests`). Above twelve distinct parameters in the two levels it falls
back to the existing `level::leq`, which can be stricter on nested `imax`.

## What differs on purpose, and what is left

- `corner-cases/nested-nonuniform-param` (outcome `either`): this was said to
  flip to a refusal. The downloadable `lean-arena-tests.tar.gz` has only
  `good/corner-cases/proof-param-ok`, so the flip could not be reproduced
  from it; treat it as unverified. No exit code changes on the arena small
  suite.
- `KL5`: `Pf : Prop | mk : Tr → Pf`, `Pf.rec (fun _ => t) h = t` for a variable
  `h`. kiota eta-expands the major premise; the official kernel does not for
  a proposition. Arena `corner-cases/eta-struct-major-and`, outcome `either`.
  Not touched.
- Levels are simplified when they are parsed (`level::max`, `level::imax`).
  On a constant that is not declared yet (in practice an occurrence of a type
  of the block being read) the parser keeps a level written `max`/`imax` that
  would simplify to a bare parameter in its written form, so `T.{max u u}`
  is refused like Lean refuses it. Everywhere else only the value of a level
  matters, and it is unchanged.
- `isReflexive`, `numNested` and, on this branch, `k` are not compared with
  the kernel's values. Nothing reads the first two.
- A signature with an undeclared constant is reported as "recursor … type
  does not match reconstructed type": the parser gives every rejection from
  the recursor comparison that message.
- The rule-list comparison is also on snd/export-names, with the same field
  and message; one of the two goes at integration.

## Follow-up (snd/inductive-audit-2)

The review of 9bb4388 found three declarations Lean 4.36 refuses and kiota
accepted (base 606c3c0 too). Each is now refused, with the same verdict as
`leanchecker` v4.36.0 on the fixture:

| Probe | Accepted before | Lean 4.36 | kiota now | Fixture |
|---|---|---|---|---|
| `R16`, `R16b` | `T \| mk : (n : N) → (t : T) → Eq' N t.0 n → T`, and the same field under `(fun _ => N)` | "unknown constant 'T.mk'" | "constructor type projects out of a type of the declaration being defined …" | `ind-ctor-field-proj-{own-type,erased}.reject`; twin `ind-ctor-field-proj-other.accept` |
| `R1`, `R1b`, `R1c` | `T.{max u u}`, `T.{imax u u}` in a field or the conclusion | "invalid occurrence of datatype 'T' being declared" | the same check, on the written level | `ind-occ-level-{max,imax}-uu.reject`, `ind-result-level-max-uu.reject`; twins `ind-occ-level-max-other-const.accept`, `ind-level-max-uu-after-block.accept` |
| `R18` | a field `_nested.Foo`, or a signature `_nested.Foo → Type` | "it uses the reserved prefix '_nested'" | "uses the reserved prefix `_nested`" | `ind-reserved-nested-prefix.reject`, `ind-sig-reserved-nested-prefix.reject`; twin `ind-reserved-nested-prefix-elsewhere.accept` |

The two arms of `check_uniform_ind_occs` no committed test reached, the
lambda-body offset (`R5`) and the let body (`R6c`), now have fixtures:
`ind-occ-{lam-offset,let-body}-nonuniform.reject`, whose recursors come from
probe builds with that arm removed, so the files are accepted by 606c3c0.

The accept twins were replayed through Lean 4.36's `addDeclCore`
(`tests/fixtures/src/inductive-audit.lean`; the `_nested` twin with its names
at the root, since that script prefixes every name). `leanchecker` itself
refuses every DSL accept fixture, old and new, with "Invalid recursor": the
DSL writes kiota's reconstructed recursors, which are not syntactically the
ones Lean generates.

## Remote validation

Strict runs on the six corpora, workflow `remote-inductive-audit`, exports
from runs 44313744961 and 44328282978. See the branch report for the FULL
lines of runs 44399951964 (f752419), 44402716855 (32b0701) and 44403696850
(3743a7a, the last change under `src/`).
