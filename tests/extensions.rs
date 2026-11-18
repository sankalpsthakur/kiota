//! A native reduction belongs to a validated declaration, not to a name
//! (`tc::extensions`).
//!
//! The `forged-*` fixtures are preludes that are not Lean's: a constant
//! carries the name of one the checker reduces natively and another
//! definition, and one theorem that is false for that definition follows it.
//! The `validated-*` twins state the same over the genuine definitions, on
//! literals only the native rule can reach. Sources and the generator are in
//! `tests/fixtures/src/extension-validation`.

use kiota::env::ExtOp;
use kiota::parser::Parser;
use kiota::tc::TcError;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn check(name: &str) -> (Parser, Result<(), TcError>) {
    let bytes = fs::read(fixture(name)).unwrap_or_else(|e| panic!("read {name}: {e}"));
    let mut parser = Parser::new();
    let verdict = parser.run(Cursor::new(bytes));
    (parser, verdict)
}

fn accept(name: &str) -> Parser {
    let (parser, verdict) = check(name);
    verdict.unwrap_or_else(|e| panic!("{name} should accept, got {e:?}"));
    parser
}

/// Rejected at the false theorem, for the reason a wrong `rfl` is.
fn reject_at_the_theorem(name: &str) -> Parser {
    let (parser, verdict) = check(name);
    match verdict {
        Err(TcError::Reject(m))
            if m.starts_with("[Forged.bad] theorem ") && m.ends_with(": value type does not match declared type") => {}
        other => panic!("{name} should reject at Forged.bad, got {other:?}"),
    }
    parser
}

/// `def Nat.add (a b : Nat) : Nat := b`, then `Nat.add 2 2 = 4` by `rfl`.
/// Lean's own kernel accepts this file: it computes with GMP for the name.
#[test]
fn a_forged_nat_add_does_not_get_the_native_rule() {
    let parser = reject_at_the_theorem("forged-nat-add.reject.ndjson");
    assert!(parser.env.ext.nat.is_some(), "`Nat` itself is genuine in this file");
    assert!(parser.env.ext.id_of(ExtOp::NatAdd).is_none());
}

#[test]
fn forged_nat_operations_do_not_get_their_native_rules() {
    for (file, op) in [
        ("forged-nat-mul.reject.ndjson", ExtOp::NatMul),
        ("forged-nat-pow.reject.ndjson", ExtOp::NatPow),
        ("forged-nat-sub.reject.ndjson", ExtOp::NatSub),
        ("forged-nat-beq.reject.ndjson", ExtOp::NatBeq),
        ("forged-nat-ble.reject.ndjson", ExtOp::NatBle),
        ("forged-nat-shiftleft.reject.ndjson", ExtOp::NatShiftLeft),
        ("forged-nat-land.reject.ndjson", ExtOp::NatLand),
        ("forged-nat-lor.reject.ndjson", ExtOp::NatLor),
        ("forged-nat-xor.reject.ndjson", ExtOp::NatXor),
        ("forged-nat-div.reject.ndjson", ExtOp::NatDiv),
        ("forged-nat-mod.reject.ndjson", ExtOp::NatMod),
        ("forged-nat-gcd.reject.ndjson", ExtOp::NatGcd),
        ("forged-nat-modcore.reject.ndjson", ExtOp::NatModCore),
        // Its own equations hold over the forged `Nat.div` they mention.
        ("forged-nat-shiftright.reject.ndjson", ExtOp::NatShiftRight),
        // `Nat.bitwise and` over a `Nat.bitwise` that returns its first number.
        ("forged-nat-bitwise.reject.ndjson", ExtOp::NatLand),
    ] {
        let parser = reject_at_the_theorem(file);
        assert!(parser.env.ext.id_of(op).is_none(), "{file}");
    }
}

/// `Nat.sub` in the forged prelude is the genuine recursion over a `Nat.pred`
/// that is the identity. Its own equations hold; it is off because the
/// `Nat.pred` they are stated with is not the predecessor.
#[test]
fn an_operation_is_only_as_good_as_the_one_it_is_stated_with() {
    let parser = reject_at_the_theorem("forged-nat-sub.reject.ndjson");
    assert!(parser.env.ext.nat_pred.is_none());
    assert!(parser.env.ext.id_of(ExtOp::NatSub).is_none());
}

/// `Nat.lor := Nat.bitwise and`: the function has the truth table of `and`.
#[test]
fn a_bitwise_operation_with_the_wrong_truth_table_gets_no_rule() {
    let parser = reject_at_the_theorem("forged-nat-lor-wrong-table.reject.ndjson");
    assert!(parser.env.ext.id_of(ExtOp::NatLor).is_none());
}

/// `ite` with its branches exchanged: `ite True (isTrue _) true false` is
/// `false` by its definition. Reading the instance's constructor and taking
/// the first branch, as `whnf_core` did for anything named `ite`, made it `true`.
#[test]
fn a_forged_ite_does_not_get_the_shortcut() {
    let parser = reject_at_the_theorem("forged-ite-swapped.reject.ndjson");
    assert!(parser.env.ext.decidable_is_true.is_some(), "`Decidable` is genuine in this file");
    assert!(parser.env.ext.id_of(ExtOp::Ite).is_none());
}

/// `dite` as an axiom: nothing reduces it, at a constructor or anywhere.
#[test]
fn a_dite_that_is_not_a_definition_does_not_get_the_shortcut() {
    let parser = reject_at_the_theorem("forged-dite-axiom.reject.ndjson");
    assert!(parser.env.ext.id_of(ExtOp::Dite).is_none());
}

#[test]
fn a_forged_decide_does_not_get_the_shortcut() {
    let parser = reject_at_the_theorem("forged-decide-swapped.reject.ndjson");
    assert!(parser.env.ext.id_of(ExtOp::Decide).is_none());
}

/// `axiom Decidable.isTrue`, beside a `Decidable` whose constructors are
/// `no` and `yes`. The genuine `ite`, `dite` and `decide` are stuck at an
/// instance built with the axiom; the shortcuts matched it by name.
#[test]
fn an_axiom_named_decidable_is_true_is_not_the_constructor() {
    for file in [
        "forged-decidable-istrue-axiom-ite.reject.ndjson",
        "forged-decidable-istrue-axiom-dite.reject.ndjson",
        "forged-decidable-istrue-axiom-decide.reject.ndjson",
    ] {
        let parser = reject_at_the_theorem(file);
        let ext = &parser.env.ext;
        assert!(ext.decidable_is_true.is_none() && ext.decidable_is_false.is_none(), "{file}");
        for op in [ExtOp::Ite, ExtOp::Dite, ExtOp::Decide] {
            assert!(ext.id_of(op).is_none(), "{file}: {op:?}");
        }
    }
}

/// `inductive Nat | succ | zero`: a literal is `succ^n zero` by the names,
/// and ι on a literal took its rule by position. A literal over this `Nat`
/// has no type.
#[test]
fn a_nat_with_its_constructors_out_of_order_has_no_literals() {
    let (parser, verdict) = check("forged-nat-ctor-order.reject.ndjson");
    match verdict {
        Err(TcError::Reject(m))
            if m == "[Forged.bad] Nat literal, but the declared `Nat` is not the kernel's `Nat`" => {}
        other => panic!("got {other:?}"),
    }
    assert!(parser.env.ext.nat.is_none() && parser.env.ext.nat_ctors.is_none());
    assert!(parser.env.ext.nat_forged);
}

/// The twins: the same statements over definitions that are the genuine
/// ones (written over the recursors), with literals near `2^200` or results
/// near `2^4000`. They pass only if the native rule is on.
#[test]
fn validated_operations_keep_their_native_rules() {
    for (file, op) in [
        ("validated-nat-add.accept.ndjson", ExtOp::NatAdd),
        ("validated-nat-mul.accept.ndjson", ExtOp::NatMul),
        ("validated-nat-pow.accept.ndjson", ExtOp::NatPow),
        ("validated-nat-sub.accept.ndjson", ExtOp::NatSub),
        ("validated-nat-beq.accept.ndjson", ExtOp::NatBeq),
        ("validated-nat-ble.accept.ndjson", ExtOp::NatBle),
        ("validated-nat-shiftleft.accept.ndjson", ExtOp::NatShiftLeft),
        ("validated-ite.accept.ndjson", ExtOp::Ite),
        ("validated-dite.accept.ndjson", ExtOp::Dite),
        ("validated-decide.accept.ndjson", ExtOp::Decide),
    ] {
        let parser = accept(file);
        assert!(parser.env.ext.id_of(op).is_some(), "{file}");
    }
}

/// Lean 4.33's own prelude, every extension constant used once
/// (`ExtAll.lean`): each one validates. A constant that failed here would
/// silently lose its fast path on every real export.
#[test]
fn every_extension_validates_on_the_real_prelude() {
    let parser = accept("genuine-extensions-all.accept.ndjson");
    let ext = &parser.env.ext;
    for op in ExtOp::ALL {
        assert!(ext.id_of(op).is_some(), "{op:?} is off on Lean's prelude");
    }
    assert!(ext.nat.is_some() && ext.nat_ctors.is_some() && !ext.nat_forged);
    assert!(ext.bool_false.is_some() && ext.bool_true.is_some());
    assert!(ext.decidable_is_false.is_some() && ext.decidable_is_true.is_some());
    assert!(ext.nat_pred.is_some() && ext.nat_bitwise.is_some());
    assert!(ext.string.is_some() && !ext.string_forged);
}

/// The Init-sized fixture whose `KIOTA_STATS` counters are compared across
/// builds: nothing it declares is off.
#[test]
fn every_extension_the_rat_fixture_declares_validates() {
    let parser = accept("rat-instEncodable-and-rec-theorem-major.accept.ndjson");
    let ext = &parser.env.ext;
    for (i, name) in parser.names.iter().enumerate() {
        if let Some(op) = ExtOp::from_spelling(name) {
            if parser.env.get(i as u32).is_some() {
                assert_eq!(ext.id_of(op), Some(i as u32), "{name} is declared and off");
            }
        }
    }
    assert!(ext.id_of(ExtOp::NatAdd).is_some() && ext.id_of(ExtOp::Decide).is_some());
}

/// The hole that remains, kept honest. `Nat.div`, `Nat.mod`, `Nat.modCore`,
/// `Nat.gcd` and `Nat.bitwise` are validated for kind, type and their values
/// on small numerals, not for their recursion. `ForgedLarge.lean` declares a
/// `Nat.div` that is division up to a dividend of 16 and `0` beyond: it gets
/// the native rule, and `Nat.div 1000 10 = 100` is accepted, as Lean's own
/// kernel accepts it. When the recursion is validated this file becomes a
/// `.reject` fixture.
#[test]
fn a_division_that_is_wrong_only_on_large_numbers_is_still_a_hole() {
    let (parser, verdict) = check("forged-nat-div-beyond-the-grid.hole.ndjson");
    assert!(verdict.is_ok(), "no longer accepted: make it a reject fixture ({verdict:?})");
    assert!(parser.env.ext.id_of(ExtOp::NatDiv).is_some());
}
