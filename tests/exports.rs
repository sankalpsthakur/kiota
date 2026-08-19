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
