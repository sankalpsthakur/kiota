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

/// `Color.rec` rules start at `True.intro` (a ctor of a different inductive).
/// Iota must not take that rule's minor for `Color.r`.
#[test]
fn forged_rule_ctor_rejects() {
    assert_reject("forged-rule-ctor.reject.ndjson");
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

/// Missing interned app/lam indices used to become expr 0 via `get_u32`.
#[test]
fn missing_app_fn_rejects() {
    assert_reject("missing-app-fn.reject.ndjson");
}

#[test]
fn missing_app_arg_rejects() {
    assert_reject("missing-app-arg.reject.ndjson");
}

#[test]
fn missing_lam_type_rejects() {
    assert_reject("missing-lam-type.reject.ndjson");
}

#[test]
fn non_u32_app_fn_rejects() {
    assert_reject("non-u32-app-fn.reject.ndjson");
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
