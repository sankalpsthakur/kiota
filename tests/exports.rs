//! In-repo export fixtures.
//!
//! Named `*.accept.ndjson` / `*.reject.ndjson` after the arena outcome.
//! `080_RBTree.id_spec` pins the iota field-then-rec order: two recursive
//! fields must become `minor f1 f2 (rec f1) (rec f2)`, not interleaved.

use kiota::parser::Parser;
use kiota::tc::TcError;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn check_file(path: &std::path::Path) -> Result<(), TcError> {
    let bytes = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut p = Parser::new();
    p.run(Cursor::new(bytes))
}

fn assert_accept(name: &str) {
    let path = fixture(name);
    check_file(&path).unwrap_or_else(|e| panic!("{name} should accept, got {e:?}"));
}

/// Like `assert_accept`, but runs on a thread with a large stack, matching
/// `main.rs`'s own `1024 * 1024 * 1024`-byte spawn for the release binary.
/// A deep, non-tail-recursive fixture (e.g. `synthetic-below-brecon-
/// countdown.accept.ndjson`'s 300-level `Below`/`Cons` chain) can overflow
/// `cargo test`'s default ~2MB thread stack in an unoptimized debug build
/// even though the same fixture is nowhere near the checker's own
/// `CONV_DEPTH` limit and passes comfortably in a release build.
fn assert_accept_deep(name: &str) {
    let name = name.to_string();
    let handle = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            let path = fixture(&name);
            check_file(&path).unwrap_or_else(|e| panic!("{name} should accept, got {e:?}"));
        })
        .expect("spawn deep-stack test thread");
    handle.join().expect("deep-stack test thread panicked");
}

fn assert_reject(name: &str) {
    let path = fixture(name);
    match check_file(&path) {
        Err(TcError::Reject(_)) => {}
        other => panic!("{name} should reject, got {other:?}"),
    }
}

#[test]
fn eq_rec_accepts() {
    assert_accept("067_eqRec.accept.ndjson");
}

#[test]
fn proof_irrel_accepts() {
    assert_accept("proof-irrel.accept.ndjson");
}

#[test]
fn alg_conv_trans_acc_left_accepts() {
    assert_accept("alg-conv-trans-acc-left.accept.ndjson");
}

#[test]
fn alg_conv_trans_acc_right_accepts() {
    assert_accept("alg-conv-trans-acc-right.accept.ndjson");
}

#[test]
fn subject_reduction_redex_accepts() {
    assert_accept("subject-reduction-redex.accept.ndjson");
}

#[test]
fn rbtree_id_spec_accepts() {
    assert_accept("080_RBTree.id_spec.accept.ndjson");
}

/// Day 12: a from-scratch, hand-generated `Nat.rec`-on-a-literal-numeral
/// countdown (`natVal: "5000"`, no declaration named after any real
/// corpus's `assemble2`/`brecOn`-generated auxiliary) — the shape this
/// whole NbE spike was originally motivated by (a recursor applied to a
/// large `Nat` numeral major), so the eager-vs-NBE `Ir` comparison this
/// fixture enables in `bench.sh` finally measures that original
/// hypothesis directly instead of by proxy through the Acc-shape
/// fixtures the spike ended up chasing correctness bugs on. `motive`
/// is constant (`fun _ => Nat`) and the `succ` minor discards its `n`
/// and returns `n_ih` unchanged, so the whole countdown reduces to
/// `Nat.zero` — the point is the 5000-step iota chain getting there, not
/// the answer.
///
/// Day 12 follow-up found this fixture's own declaration check never
/// actually forces that chain: `Nat.rec`'s type-checking rule verifies
/// the minors generically (in the bound `n`, not the literal), and the
/// declared type here is the same *symbolic* `Nat`, so `KIOTA_STATS` is
/// completely flat regardless of the literal's value — it measures fixed
/// overhead, not a 5000-step reduction. Left as-is (still a valid,
/// accepting fixture, just not informative about the countdown's own
/// cost) rather than silently reinterpreted after the fact; see
/// `synthetic_below_brecon_countdown_accepts` below for a fixture that
/// verifiably does force the chain (`KIOTA_STATS` scales with depth).
#[test]
fn synthetic_nat_rec_countdown_accepts() {
    assert_accept("synthetic-nat-rec-countdown.accept.ndjson");
}

/// Day 12 (second pass): a "course-of-values"/`brecOn`-shaped fixture,
/// not a plain `Nat.rec`-on-a-literal one. `Below : Nat -> Sort 1` is
/// *itself* defined by `Nat.rec`, building a structurally new wrapper at
/// every level (`Cons Nat (Cons Nat ( ... Nat))`, growing by one `Cons`
/// layer per level — the synthetic stand-in for real Lean's
/// `Nat.below`'s `PProd`-nested table), and `countdown`'s own minor reads
/// the recursive occurrence `ih : Below n` directly to build the next
/// level's value (`Cons.cons (Below n) n ih`). Depth 300 (in the 200-500
/// range suggested as a lighter alternative to a 5000-step literal
/// countdown): the declared type is deliberately the *explicit*
/// hand-unfolded normal form (300 nested `Cons` applications, not
/// `Below 300` symbolically) so `is_def_eq` cannot dispatch by matching
/// `App(Below, _)` heads on both sides and must actually `whnf`/unfold
/// `Below`'s recursive definition through all 300 levels to compare
/// structurally — confirmed by `KIOTA_STATS` scaling with depth (unlike
/// the plain-`Nat.rec` fixture above). Never named after `assemble2` or
/// any real declaration; `Cons`/`Below`/`countdown` are generic.
#[test]
fn synthetic_below_brecon_countdown_accepts() {
    assert_accept_deep("synthetic-below-brecon-countdown.accept.ndjson");
}

/// Day 14: the leftover hypothesis named at the end of the `Below`-as-
/// named-`Def` fixture above -- "the growing structure must be an inline,
/// non-shared subterm, not repeated calls to a named `Def`." `countdown`
/// here is *not* a recursor application at all: it's 250 nested beta-
/// redexes, `(fun (ih:Dom_249) => Cons.mk Dom_249 0 ih) ( ... (fun
/// (ih:Dom_0) => Cons.mk Dom_0 0 ih) Nat.zero ...)`, where `Dom_k` (the
/// k-`Cons`-layer-deep type at level `k`) is rebuilt from scratch --
/// fresh `App(Cons, ...)` nodes, never referencing any earlier level's
/// nodes -- at *every* occurrence (the lambda's own domain and `Cons.mk`'s
/// own type parameter are separate rebuilds too), so neither structural
/// interning nor `infer_cache`'s pointer-keyed memoization can short-
/// circuit repeat work across levels. The declared type is likewise the
/// explicit, independently-rebuilt 250-layer normal form, not a symbolic
/// reference. Depth 250 (in the suggested 200-500 range). Never named
/// after `assemble2`/`utf8DecodeChar?`; `Cons`/`countdown` are generic.
///
/// This is the fixture that actually reproduces superlinear eager cost:
/// callgrind `Ir` at N=40/80/160 grows ~3.6x-3.8x per doubling of N (not
/// ~2x, i.e. not linear) -- but NBE grows the same way and is *slower*,
/// not faster, at every depth tried (~1.4x-1.46x). See the PR for the
/// full numbers and the resulting decision.
#[test]
fn synthetic_below_inline_unshared_accepts() {
    assert_accept_deep("synthetic-below-inline-unshared.accept.ndjson");
}

#[test]
fn bad_def_rejects() {
    assert_reject("002_badDef.reject.ndjson");
}

#[test]
fn non_prop_thm_rejects() {
    assert_reject("012_nonPropThm.reject.ndjson");
}

#[test]
fn extra_rec_rejects() {
    assert_reject("extra-rec.reject.ndjson");
}

/// Recursor identity is rule constructors / `all ∩ group`, not `I.rec`.
/// `elim` is a well-typed recursor for `False`; a pretty-name gate used to reject it.
#[test]
fn extra_rec_all_field_not_pretty_name_accepts() {
    assert_accept("extra-rec-alt-name.accept.ndjson");
}

#[test]
fn extra_rec_sole_false_type_rejects() {
    assert_reject("extra-rec-sole-false-typ.reject.ndjson");
}

#[test]
fn unsafe_axiom_rejects() {
    assert_reject("unsafe-axiom.reject.ndjson");
}

#[test]
fn partial_def_rejects() {
    assert_reject("partial-def.reject.ndjson");
}

#[test]
fn quot_false_rejects() {
    assert_reject("quot-false.reject.ndjson");
}

#[test]
fn missing_required_u32_rejects() {
    assert_reject("missing-required-u32.reject.ndjson");
}

#[test]
fn missing_ctor_num_fields_rejects() {
    assert_reject("missing-ctor-num-fields.reject.ndjson");
}

#[test]
fn missing_rec_num_minors_rejects() {
    assert_reject("missing-rec-num-minors.reject.ndjson");
}

#[test]
fn missing_decl_name_rejects() {
    assert_reject("missing-decl-name.reject.ndjson");
}

#[test]
fn missing_decl_type_rejects() {
    assert_reject("missing-decl-type.reject.ndjson");
}

#[test]
fn non_u32_num_params_rejects() {
    assert_reject("non-u32-num-params.reject.ndjson");
}

/// Recursor type `False → False` is a Pi but not a recursor telescope.
#[test]
fn extra_rec_wrong_pi_type_rejects() {
    assert_reject("extra-rec-wrong-pi-type.reject.ndjson");
}

#[test]
fn quot_wrong_pi_rejects() {
    assert_reject("quot-wrong-pi.reject.ndjson");
}

#[test]
fn quot_wrong_kind_rejects() {
    assert_reject("quot-wrong-kind.reject.ndjson");
}

#[test]
fn quot_bare_sort_rejects() {
    assert_reject("quot-bare-sort.reject.ndjson");
}

#[test]
fn missing_rec_rule_ctor_rejects() {
    assert_reject("missing-rec-rule-ctor.reject.ndjson");
}

#[test]
fn missing_rec_rule_nfields_rejects() {
    assert_reject("missing-rec-rule-nfields.reject.ndjson");
}

#[test]
fn missing_rec_rule_rhs_rejects() {
    assert_reject("missing-rec-rule-rhs.reject.ndjson");
}

#[test]
fn unknown_expr_kind_rejects() {
    assert_reject("unknown-expr-kind.reject.ndjson");
}

/// Missing `hints` used to become `Regular(0)` and unfold like a transparent def.
#[test]
fn missing_hints_unfolds_rejects() {
    assert_reject("missing-hints-unfolds.reject.ndjson");
}

/// `numNested: 9` is not extra-rec allowance; nested types come from ctor fields.
#[test]
fn inflated_num_nested_rejects() {
    assert_reject("inflated-numNested.reject.ndjson");
}

#[test]
fn missing_is_rec_rejects() {
    assert_reject("missing-isRec.reject.ndjson");
}

/// 2-Pi+Sort whose first domain is `False`, not `Sort`.
#[test]
fn quot_2pi_false_dom_rejects() {
    assert_reject("quot-2pi-false-dom.reject.ndjson");
}

/// `inductive Bad.{u} : Sort u | mk : Sort (u+1) → Bad`.
#[test]
fn ctor_field_univ_open_rejects() {
    assert_reject("ctor-field-univ-open.reject.ndjson");
}

/// `Neg α` has a negative field; `Bad` nested as `Neg Bad` must not pass
/// just because `Neg` is a previously defined inductive.
#[test]
fn nested_neg_functor_rejects() {
    assert_reject("nested-neg-functor.reject.ndjson");
}

/// `List` is strictly positive; `Tree` with a `List Tree` field is a nested
/// inductive Lean accepts (`Syntax` is the same shape).
#[test]
fn nested_list_tree_accepts() {
    assert_accept("nested-list-tree.accept.ndjson");
}

// ---- lean-kernel-arena live false accepts (fetched from
// leanprover/lean-kernel-arena @ 1df91b3909dfbf85de17c23190b5059e74d5c60c's
// `lean-arena-tests.tar.gz`, verbatim, not hand-written) ----
//
// The live arena board (results.json, 2026-08-26 11:02:30 UTC, run
// 32952787023) had `kiota` accepting all six of these on `main 0.1.0 @
// 58e8636`. On this branch, three already rejected before this pass
// (`tutorial-094-projProp6`, `tutorial-144-falseFromUnsafe`,
// `tutorial-145-falseFromPartial` — added here to lock that in against
// regression); the other three were genuine, fixed bugs in this pass.

/// A `Prop`-valued inductive (`NewBool`) with two constructors whose
/// recursor is universe-polymorphic in the motive's own sort, i.e.
/// allows "large elimination" — computing a real `Bool` from a proof.
/// Combined with proof irrelevance (any two proofs of a `Prop` are
/// equal), this proves `False`. Real Lean's kernel restricts a
/// multi-constructor Prop inductive's recursor to `Sort 0` motives only;
/// this checker previously never validated that at all. Fixed in
/// `handle_inductive_block` (parser.rs): a Prop-valued inductive with
/// two or more constructors must have its recursor's motive fixed at
/// `Sort 0`, checked structurally (peeling the recursor's own Pi
/// telescope to the motive parameter's codomain sort), not by name.
#[test]
fn large_elim_prop_bool_rejects() {
    assert_reject("large-elim-prop-bool.reject.ndjson");
}

/// A constructor named `rogue`, typed `False`, whose `induct` field
/// names `Orphan` — an inductive this export never declares anywhere.
/// This checker previously registered every entry in an `inductive`
/// block's `ctors` array unconditionally, without checking that
/// `induct` names a real inductive declared in the same block, or that
/// the named inductive's own `ctors` list actually includes this
/// constructor at the claimed index. Fixed in `handle_inductive_block`:
/// every constructor is now cross-checked against its claimed owner's
/// own declared `ctors` list before being registered.
#[test]
fn orphan_ctor_rejects() {
    assert_reject("orphan-ctor.reject.ndjson");
}

/// `theorem selfProof : ∀ (p : Prop), p := selfProof` — a declaration
/// whose own value references its own (not yet defined) name. Real
/// Lean's kernel type-checks a declaration before adding it to the
/// environment, so a self-reference is an unresolved identifier. This
/// checker instead inserts each declaration before checking it
/// (`handle_def_like` then `check_decl`), which let a self-reference
/// resolve to the declaration's own declared type and match trivially.
/// Fixed in `check_decl` (tc.rs): a declaration's value may not mention
/// its own name, checked structurally for any name, not this one.
#[test]
fn tutorial_014_self_proof_rejects() {
    assert_reject("tutorial-014-selfProof.reject.ndjson");
}

/// Projecting a `Type`-sorted field of a structure reached only through
/// a genuine `Prop`-valued value along the way. Already rejected on this
/// branch before this pass (`cannot project a Type field from a Prop
/// structure`); added here as a permanent regression fixture.
#[test]
fn tutorial_094_proj_prop6_rejects() {
    assert_reject("tutorial-094-projProp6.reject.ndjson");
}

/// `def unsafeLoop : False := unsafeLoop` (self-referential, but marked
/// `unsafe`, so self-reference is legitimate) followed by
/// `theorem falseFromUnsafe : False := unsafeLoop` — a safe theorem
/// depending on an unsafe definition's value. Already rejected on this
/// branch before this pass (the parser refuses any `unsafe`-marked
/// `def`/`opaque` outright, so `unsafeLoop` itself never reaches the
/// environment); added here as a permanent regression fixture.
#[test]
fn tutorial_144_false_from_unsafe_rejects() {
    assert_reject("tutorial-144-falseFromUnsafe.reject.ndjson");
}

/// Same shape as `144_falseFromUnsafe` with `partial` in place of
/// `unsafe`. Already rejected on this branch before this pass; added
/// here as a permanent regression fixture.
#[test]
fn tutorial_145_false_from_partial_rejects() {
    assert_reject("tutorial-145-falseFromPartial.reject.ndjson");
}
