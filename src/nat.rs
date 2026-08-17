//! Minimal native Nat reduction helpers (pure, no environment).
//!
//! Covers the leanest set needed for arena Acc / prelude gaps:
//! succ-of-lit, add of lits, add-n-1 → succ, beq of numerals, OfNat strip.

use crate::expr::{self, Expr, ExprData, Lit};
use num_bigint::BigUint;

/// Direct `Lit::Nat` payload, if any.
pub fn as_lit(e: &Expr) -> Option<&BigUint> {
    match &***e {
        ExprData::Lit(Lit::Nat(n)) => Some(n),
        _ => None,
    }
}

pub fn mk_lit(n: BigUint) -> Expr {
    expr::lit_nat(n)
}

pub fn succ_value(n: &BigUint) -> BigUint {
    n + 1u32
}

pub fn add_values(a: &BigUint, b: &BigUint) -> BigUint {
    a + b
}

pub fn mul_values(a: &BigUint, b: &BigUint) -> BigUint {
    a * b
}

pub fn sub_values(a: &BigUint, b: &BigUint) -> BigUint {
    if a >= b {
        a - b
    } else {
        BigUint::from(0u32)
    }
}

pub fn div_values(a: &BigUint, b: &BigUint) -> BigUint {
    if *b == BigUint::from(0u32) {
        BigUint::from(0u32)
    } else {
        a / b
    }
}

pub fn mod_values(a: &BigUint, b: &BigUint) -> BigUint {
    if *b == BigUint::from(0u32) {
        a.clone()
    } else {
        a % b
    }
}

pub fn shift_left_values(a: &BigUint, b: &BigUint) -> Option<BigUint> {
    if *b == BigUint::from(0u32) {
        return Some(a.clone());
    }
    if b.bits() > 16 {
        return None;
    }
    let shift = b.to_u64_digits().first().copied().unwrap_or(0) as usize;
    if shift > 100_000 {
        return None;
    }
    Some(a << shift)
}

pub fn shift_right_values(a: &BigUint, b: &BigUint) -> BigUint {
    if *b == BigUint::from(0u32) {
        return a.clone();
    }
    if b.bits() > 16 {
        return BigUint::from(0u32);
    }
    let shift = b.to_u64_digits().first().copied().unwrap_or(0) as usize;
    a >> shift
}

pub fn land_values(a: &BigUint, b: &BigUint) -> BigUint {
    a & b
}

pub fn lor_values(a: &BigUint, b: &BigUint) -> BigUint {
    a | b
}

pub fn xor_values(a: &BigUint, b: &BigUint) -> BigUint {
    a ^ b
}

pub fn ble_values(a: &BigUint, b: &BigUint) -> bool {
    a <= b
}

pub fn pow_values(a: &BigUint, b: &BigUint) -> Option<BigUint> {
    if *b == BigUint::from(0u32) {
        return Some(BigUint::from(1u32));
    }
    if b.bits() > 16 {
        return None;
    }
    let exp = b.to_u64_digits().first().copied().unwrap_or(0) as u32;
    Some(a.pow(exp))
}

/// Predecessor: `lit (n+1)` or `succ e` → inner. `0` / `zero` is `None`.
pub fn pred(e: &Expr, zero: u32, succ: u32) -> Option<Expr> {
    if let Some(n) = as_lit(e) {
        if *n == BigUint::from(0u32) {
            return None;
        }
        return Some(mk_lit(n - 1u32));
    }
    match &***e {
        ExprData::App(f, a) if matches!(&***f, ExprData::Const(s, us) if *s == succ && us.is_empty()) => {
            Some(a.clone())
        }
        ExprData::Const(z, us) if *z == zero && us.is_empty() => None,
        _ => None,
    }
}

pub fn beq_values(a: &BigUint, b: &BigUint) -> bool {
    a == b
}

/// `Nat.zero` or `lit 0`.
pub fn is_zero(e: &Expr, zero: u32) -> bool {
    if let Some(n) = as_lit(e) {
        return *n == BigUint::from(0u32);
    }
    matches!(&***e, ExprData::Const(z, us) if *z == zero && us.is_empty())
}

/// `lit 1`, `Nat.succ Nat.zero`, or `Nat.succ (lit 0)`.
pub fn is_one(e: &Expr, zero: u32, succ: u32) -> bool {
    if let Some(n) = as_lit(e) {
        return *n == BigUint::from(1u32);
    }
    match &***e {
        ExprData::App(f, a) => {
            matches!(&***f, ExprData::Const(s, us) if *s == succ && us.is_empty())
                && is_zero(a, zero)
        }
        _ => false,
    }
}

/// Interpret a closed numeral: lit, zero, or a finite `succ` tower over those.
pub fn numeral_value(e: &Expr, zero: u32, succ: u32) -> Option<BigUint> {
    if let Some(n) = as_lit(e) {
        return Some(n.clone());
    }
    if is_zero(e, zero) {
        return Some(BigUint::from(0u32));
    }
    match &***e {
        ExprData::App(f, a) => {
            if matches!(&***f, ExprData::Const(s, us) if *s == succ && us.is_empty()) {
                let v = numeral_value(a, zero, succ)?;
                return Some(succ_value(&v));
            }
            None
        }
        _ => None,
    }
}

/// `OfNat.ofNat` head applied to at least `[α, n, inst, …]`: return `n` when `α` is `Nat`.
pub fn of_nat_value(args: &[Expr], nat_ty: u32) -> Option<Expr> {
    if args.len() < 3 {
        return None;
    }
    match &**args[0] {
        ExprData::Const(t, _) if *t == nat_ty => {
            if as_lit(&args[1]).is_some() {
                Some(args[1].clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build `Nat.succ n` (no universes).
pub fn mk_succ(succ: u32, n: Expr) -> Expr {
    expr::app(expr::const_(succ, vec![]), n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr;

    fn lit(n: u32) -> Expr {
        mk_lit(BigUint::from(n))
    }

    #[test]
    fn succ_of_zero_lit() {
        assert_eq!(succ_value(&BigUint::from(0u32)), BigUint::from(1u32));
        assert_eq!(succ_value(&BigUint::from(41u32)), BigUint::from(42u32));
    }

    #[test]
    fn mul_sub_ble_lits() {
        assert_eq!(
            mul_values(&BigUint::from(3u32), &BigUint::from(4u32)),
            BigUint::from(12u32)
        );
        assert_eq!(
            sub_values(&BigUint::from(5u32), &BigUint::from(2u32)),
            BigUint::from(3u32)
        );
        assert_eq!(
            sub_values(&BigUint::from(2u32), &BigUint::from(5u32)),
            BigUint::from(0u32)
        );
        assert!(ble_values(&BigUint::from(2u32), &BigUint::from(2u32)));
        assert!(!ble_values(&BigUint::from(3u32), &BigUint::from(2u32)));
        assert_eq!(
            pow_values(&BigUint::from(2u32), &BigUint::from(3u32)),
            Some(BigUint::from(8u32))
        );
        assert_eq!(
            pow_values(&BigUint::from(5u32), &BigUint::from(0u32)),
            Some(BigUint::from(1u32))
        );
    }

    #[test]
    fn pred_succ_and_lit() {
        let zero = 10u32;
        let succ = 11u32;
        assert!(pred(&lit(0), zero, succ).is_none());
        assert_eq!(
            as_lit(&pred(&lit(3), zero, succ).unwrap()).cloned(),
            Some(BigUint::from(2u32))
        );
        let s = expr::app(expr::const_(succ, vec![]), lit(7));
        assert_eq!(
            as_lit(&pred(&s, zero, succ).unwrap()).cloned(),
            Some(BigUint::from(7u32))
        );
        assert!(pred(&expr::const_(zero, vec![]), zero, succ).is_none());
        assert!(pred(&expr::bvar(0), zero, succ).is_none());
    }

    #[test]
    fn add_lits() {
        assert_eq!(
            add_values(&BigUint::from(2u32), &BigUint::from(3u32)),
            BigUint::from(5u32)
        );
        assert_eq!(
            add_values(&BigUint::from(0u32), &BigUint::from(7u32)),
            BigUint::from(7u32)
        );
    }

    #[test]
    fn beq_lits() {
        assert!(beq_values(&BigUint::from(0u32), &BigUint::from(0u32)));
        assert!(!beq_values(&BigUint::from(0u32), &BigUint::from(1u32)));
    }

    #[test]
    fn as_lit_only_nats() {
        assert_eq!(
            as_lit(&lit(3)).map(|n| n.clone()),
            Some(BigUint::from(3u32))
        );
        assert!(as_lit(&expr::const_(1, vec![])).is_none());
        assert!(as_lit(&expr::bvar(0)).is_none());
    }

    #[test]
    fn is_zero_lit_and_const() {
        let zero = 10u32;
        assert!(is_zero(&lit(0), zero));
        assert!(!is_zero(&lit(1), zero));
        assert!(is_zero(&expr::const_(zero, vec![]), zero));
        assert!(!is_zero(&expr::const_(11, vec![]), zero));
    }

    #[test]
    fn is_one_shapes() {
        let zero = 10u32;
        let succ = 11u32;
        assert!(is_one(&lit(1), zero, succ));
        assert!(!is_one(&lit(0), zero, succ));
        assert!(!is_one(&lit(2), zero, succ));
        let succ_zero = expr::app(expr::const_(succ, vec![]), expr::const_(zero, vec![]));
        assert!(is_one(&succ_zero, zero, succ));
        let succ_lit0 = expr::app(expr::const_(succ, vec![]), lit(0));
        assert!(is_one(&succ_lit0, zero, succ));
        let succ_lit1 = expr::app(expr::const_(succ, vec![]), lit(1));
        assert!(!is_one(&succ_lit1, zero, succ));
    }

    #[test]
    fn numeral_value_succ_tower() {
        let zero = 10u32;
        let succ = 11u32;
        assert_eq!(
            numeral_value(&expr::const_(zero, vec![]), zero, succ),
            Some(BigUint::from(0u32))
        );
        let one = expr::app(expr::const_(succ, vec![]), expr::const_(zero, vec![]));
        assert_eq!(numeral_value(&one, zero, succ), Some(BigUint::from(1u32)));
        let two = expr::app(expr::const_(succ, vec![]), one);
        assert_eq!(numeral_value(&two, zero, succ), Some(BigUint::from(2u32)));
        assert_eq!(
            numeral_value(&lit(5), zero, succ),
            Some(BigUint::from(5u32))
        );
        assert!(numeral_value(&expr::bvar(0), zero, succ).is_none());
    }

    #[test]
    fn of_nat_strips_when_type_is_nat() {
        let nat_ty = 1u32;
        let args = vec![
            expr::const_(nat_ty, vec![]),
            lit(1),
            expr::const_(99, vec![]),
        ];
        let v = of_nat_value(&args, nat_ty).expect("ofNat");
        assert_eq!(as_lit(&v).map(|n| n.clone()), Some(BigUint::from(1u32)));
        // wrong type
        assert!(of_nat_value(
            &[expr::const_(2, vec![]), lit(1), expr::const_(99, vec![])],
            nat_ty
        )
        .is_none());
        // non-lit value
        assert!(of_nat_value(
            &[
                expr::const_(nat_ty, vec![]),
                expr::bvar(0),
                expr::const_(99, vec![])
            ],
            nat_ty
        )
        .is_none());
    }

    #[test]
    fn mk_succ_builds_app() {
        let s = mk_succ(3, lit(0));
        match &**s {
            ExprData::App(f, a) => {
                assert!(matches!(&***f, ExprData::Const(3, us) if us.is_empty()));
                assert_eq!(as_lit(a).map(|n| n.clone()), Some(BigUint::from(0u32)));
            }
            _ => panic!("expected app"),
        }
    }
}
