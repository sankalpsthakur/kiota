use crate::env::{ConstantInfo, Environment, QuotKind, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr, ExprData, Lit};
use crate::level::{self, Level};
use crate::nat;
use num_bigint::{BigInt, BigUint, Sign};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

thread_local! {
    static DEFEQ_DEPTH: Cell<u32> = const { Cell::new(0) };
    static WHNF_DEPTH: Cell<u32> = const { Cell::new(0) };
}

#[derive(Debug)]
pub enum TcError {
    Reject(String),
    Decline(String),
    Other(String),
}
pub type R<T> = Result<T, TcError>;

fn reject<T>(msg: impl Into<String>) -> R<T> {
    Err(TcError::Reject(msg.into()))
}

/// Lean `Int.pow m n`: `|m|^n` with sign `sign(m)^n`. `n = 0` yields `1`.
fn int_pow(base: &BigInt, exp: &BigUint) -> Option<BigInt> {
    if *exp == BigUint::from(0u32) {
        return Some(BigInt::from(1));
    }
    if exp.bits() > 16 {
        return None;
    }
    let e = exp.to_u32_digits().first().copied().unwrap_or(0);
    let mag = base.magnitude().pow(e);
    if base.sign() != Sign::Minus || e % 2 == 0 {
        Some(BigInt::from(mag))
    } else {
        Some(-BigInt::from(mag))
    }
}

/// Lean `Int.emod a (ofNat m)` for `m : Nat`: remainder in `[0, m)`. `m = 0` yields `a`.
fn int_emod_nat(a: &BigInt, m: &BigUint) -> BigInt {
    if *m == BigUint::from(0u32) {
        return a.clone();
    }
    let mi = BigInt::from(m.clone());
    let r = a % &mi;
    if r.sign() == Sign::Minus {
        r + mi
    } else {
        r
    }
}

/// Lean `Int.bmod x m`: balanced remainder in `(-⌈m/2⌉, ⌊m/2⌋]`.
fn int_bmod(x: &BigInt, m: &BigUint) -> BigInt {
    if *m == BigUint::from(0u32) {
        return x.clone();
    }
    let r = int_emod_nat(x, m);
    let half = BigInt::from((m + 1u32) / 2u32);
    if r < half {
        r
    } else {
        r - BigInt::from(m.clone())
    }
}

/// Lean `Int.ediv` (Euclidean). `y = 0` yields `0`.
fn int_ediv(a: &BigInt, b: &BigInt) -> BigInt {
    if b.sign() == Sign::NoSign {
        return BigInt::from(0);
    }
    let a_neg = a.sign() == Sign::Minus;
    let b_neg = b.sign() == Sign::Minus;
    let babs = BigInt::from(b.magnitude().clone());
    if !a_neg && !b_neg {
        a / b
    } else if !a_neg && b_neg {
        -(a / &babs)
    } else if a_neg && !b_neg {
        let m: BigInt = -a - BigInt::from(1);
        let q: BigInt = m / b + BigInt::from(1);
        -q
    } else {
        let m: BigInt = -a - BigInt::from(1);
        m / babs + BigInt::from(1)
    }
}

/// Lean `Int.emod a b`: remainder in `[0, |b|)`. `b = 0` yields `a`.
fn int_emod(a: &BigInt, b: &BigInt) -> BigInt {
    if b.sign() == Sign::NoSign {
        return a.clone();
    }
    int_emod_nat(a, b.magnitude())
}

/// Lean `Int.Linear.cdiv a b` = `-((-a) / b)` (Euclidean `/`).
fn int_cdiv(a: &BigInt, b: &BigInt) -> BigInt {
    -int_ediv(&-a, b)
}

/// Lean `Int.Linear.cmod a b` = `-((-a) % b)`.
fn int_cmod(a: &BigInt, b: &BigInt) -> BigInt {
    -int_emod(&-a, b)
}

fn is_int_linear_ident(name: &str, ident: &str) -> bool {
    if name == ident {
        return true;
    }
    if !name.ends_with(ident) {
        return false;
    }
    let rest = &name[..name.len() - ident.len()];
    rest.ends_with('.') && (name.contains("Int.Linear") || name == ident)
}

/// Closed `Int.Linear.Poly` spine (larger `Var` first). Used to evaluate
/// `combine_mul_k` without peeling `hugeFuel` `Nat.rec`. Do not intercept
/// `Poly.beq'` itself: `beq'_eq` / grind need the `Poly.rec` unfolding.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LinearPoly {
    Num(BigInt),
    Add(BigInt, BigUint, Box<LinearPoly>),
}

impl LinearPoly {
    fn coeff(&self, x: &BigUint) -> BigInt {
        match self {
            LinearPoly::Num(_) => BigInt::from(0),
            LinearPoly::Add(k, v, p) => {
                if v == x {
                    k.clone()
                } else {
                    p.coeff(x)
                }
            }
        }
    }

    fn mul(&self, k: &BigInt) -> Self {
        if k.sign() == Sign::NoSign {
            return LinearPoly::Num(BigInt::from(0));
        }
        self.mul_nz(k)
    }

    fn mul_nz(&self, k: &BigInt) -> Self {
        match self {
            LinearPoly::Num(c) => LinearPoly::Num(k * c),
            LinearPoly::Add(a, v, p) => LinearPoly::Add(k * a, v.clone(), Box::new(p.mul_nz(k))),
        }
    }

    fn add_const(&self, k: &BigInt) -> Self {
        match self {
            LinearPoly::Num(c) => LinearPoly::Num(c + k),
            LinearPoly::Add(a, v, p) => {
                LinearPoly::Add(a.clone(), v.clone(), Box::new(p.add_const(k)))
            }
        }
    }

    fn combine_mul_k(a: &BigInt, b: &BigInt, p1: &Self, p2: &Self) -> Self {
        if a.sign() == Sign::NoSign {
            return p2.mul(b);
        }
        if b.sign() == Sign::NoSign {
            return p1.mul(a);
        }
        Self::merge(a, b, p1, p2)
    }

    fn merge(a: &BigInt, b: &BigInt, p1: &Self, p2: &Self) -> Self {
        match (p1, p2) {
            (LinearPoly::Num(k1), LinearPoly::Num(k2)) => LinearPoly::Num(a * k1 + b * k2),
            (LinearPoly::Num(_), LinearPoly::Add(a2, x2, p2t)) => {
                LinearPoly::Add(b * a2, x2.clone(), Box::new(Self::merge(a, b, p1, p2t)))
            }
            (LinearPoly::Add(a1, x1, p1t), LinearPoly::Num(_)) => {
                LinearPoly::Add(a * a1, x1.clone(), Box::new(Self::merge(a, b, p1t, p2)))
            }
            (LinearPoly::Add(a1, x1, p1t), LinearPoly::Add(a2, x2, p2t)) => {
                if x1 == x2 {
                    let c = a * a1 + b * a2;
                    if c.sign() == Sign::NoSign {
                        Self::merge(a, b, p1t, p2t)
                    } else {
                        LinearPoly::Add(c, x1.clone(), Box::new(Self::merge(a, b, p1t, p2t)))
                    }
                } else if x2 < x1 {
                    LinearPoly::Add(a * a1, x1.clone(), Box::new(Self::merge(a, b, p1t, p2)))
                } else {
                    LinearPoly::Add(b * a2, x2.clone(), Box::new(Self::merge(a, b, p1, p2t)))
                }
            }
        }
    }

    fn insert(&self, k: &BigInt, v: &BigUint) -> Self {
        match self {
            LinearPoly::Num(c) => {
                LinearPoly::Add(k.clone(), v.clone(), Box::new(LinearPoly::Num(c.clone())))
            }
            LinearPoly::Add(k2, v2, p) => {
                if v2 < v {
                    LinearPoly::Add(k.clone(), v.clone(), Box::new(self.clone()))
                } else if v == v2 {
                    let s = k + k2;
                    if s.sign() == Sign::NoSign {
                        (**p).clone()
                    } else {
                        LinearPoly::Add(s, v2.clone(), p.clone())
                    }
                } else {
                    LinearPoly::Add(k2.clone(), v2.clone(), Box::new(p.insert(k, v)))
                }
            }
        }
    }

    fn beq(&self, other: &Self) -> bool {
        match (self, other) {
            (LinearPoly::Num(a), LinearPoly::Num(b)) => a == b,
            (LinearPoly::Add(k1, v1, p1), LinearPoly::Add(k2, v2, p2)) => {
                k1 == k2 && v1 == v2 && p1.beq(p2)
            }
            _ => false,
        }
    }

    fn lead_coeff(&self) -> BigInt {
        match self {
            LinearPoly::Add(a, _, _) => a.clone(),
            LinearPoly::Num(_) => BigInt::from(1),
        }
    }

    fn get_const(&self) -> BigInt {
        match self {
            LinearPoly::Num(k) => k.clone(),
            LinearPoly::Add(_, _, p) => p.get_const(),
        }
    }

    fn div_coeffs(&self, k: &BigInt) -> bool {
        if k.sign() == Sign::NoSign {
            return false;
        }
        match self {
            LinearPoly::Num(_) => true,
            LinearPoly::Add(a, _, p) => int_emod(a, k).sign() == Sign::NoSign && p.div_coeffs(k),
        }
    }

    fn div(&self, k: &BigInt) -> Self {
        match self {
            LinearPoly::Num(c) => LinearPoly::Num(int_cdiv(c, k)),
            LinearPoly::Add(a, v, p) => {
                LinearPoly::Add(int_ediv(a, k), v.clone(), Box::new(p.div(k)))
            }
        }
    }

    fn nat_abs(k: &BigInt) -> BigInt {
        BigInt::from(k.magnitude().clone())
    }

    fn normalize(&self) -> Self {
        match self {
            LinearPoly::Num(k) => LinearPoly::Num(k.clone()),
            LinearPoly::Add(k, v, p) => p.normalize().insert(k, v),
        }
    }
}

/// Closed `Int.Linear.Expr`. `norm` = `toPoly'.norm` (insert-sort).
#[derive(Clone, Debug)]
enum LinearExpr {
    Num(BigInt),
    Var(BigUint),
    Add(Box<LinearExpr>, Box<LinearExpr>),
    Sub(Box<LinearExpr>, Box<LinearExpr>),
    Neg(Box<LinearExpr>),
    MulL(BigInt, Box<LinearExpr>),
    MulR(Box<LinearExpr>, BigInt),
}

impl LinearExpr {
    fn to_poly(&self) -> LinearPoly {
        self.go(&BigInt::from(1), LinearPoly::Num(BigInt::from(0)))
    }

    fn go(&self, coeff: &BigInt, acc: LinearPoly) -> LinearPoly {
        match self {
            LinearExpr::Num(k) => {
                if k.sign() == Sign::NoSign {
                    acc
                } else {
                    acc.add_const(&(coeff * k))
                }
            }
            LinearExpr::Var(v) => LinearPoly::Add(coeff.clone(), v.clone(), Box::new(acc)),
            LinearExpr::Add(a, b) => a.go(coeff, b.go(coeff, acc)),
            LinearExpr::Sub(a, b) => a.go(coeff, b.go(&-coeff, acc)),
            LinearExpr::Neg(a) => a.go(&-coeff, acc),
            LinearExpr::MulL(k, a) | LinearExpr::MulR(a, k) => {
                if k.sign() == Sign::NoSign {
                    acc
                } else {
                    a.go(&(coeff * k), acc)
                }
            }
        }
    }

    fn norm(&self) -> LinearPoly {
        self.to_poly().normalize()
    }
}

fn is_commring_ident(name: &str, ident: &str) -> bool {
    if !name.contains("CommRing") {
        return false;
    }
    if name == ident {
        return true;
    }
    if !name.ends_with(ident) {
        return false;
    }
    let rest = &name[..name.len() - ident.len()];
    rest.ends_with('.')
}

/// Closed `Lean.Grind.CommRing` monomials: smaller `Var` first (`Power.varLt`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct CrPower {
    x: BigUint,
    k: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CrMon {
    Unit,
    Mult(CrPower, Box<CrMon>),
}

impl CrMon {
    fn of_var(x: BigUint) -> Self {
        CrMon::Mult(
            CrPower {
                x,
                k: BigUint::from(1u32),
            },
            Box::new(CrMon::Unit),
        )
    }

    fn of_pow(x: BigUint, k: BigUint) -> Self {
        CrMon::Mult(CrPower { x, k }, Box::new(CrMon::Unit))
    }

    fn degree(&self) -> BigUint {
        match self {
            CrMon::Unit => BigUint::from(0u32),
            CrMon::Mult(pw, m) => &pw.k + m.degree(),
        }
    }

    fn var_lt(a: &CrPower, b: &CrPower) -> bool {
        a.x < b.x
    }

    fn power_revlex(k1: &BigUint, k2: &BigUint) -> std::cmp::Ordering {
        if k1 < k2 {
            std::cmp::Ordering::Greater
        } else if k2 < k1 {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Equal
        }
    }

    fn revlex(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (CrMon::Unit, CrMon::Unit) => std::cmp::Ordering::Equal,
            (CrMon::Unit, CrMon::Mult(..)) => std::cmp::Ordering::Greater,
            (CrMon::Mult(..), CrMon::Unit) => std::cmp::Ordering::Less,
            (CrMon::Mult(pw1, m1), CrMon::Mult(pw2, m2)) => {
                if pw1.x == pw2.x {
                    m1.revlex(m2).then(Self::power_revlex(&pw1.k, &pw2.k))
                } else if pw1.x < pw2.x {
                    m1.revlex(other).then(std::cmp::Ordering::Less)
                } else {
                    self.revlex(m2).then(std::cmp::Ordering::Greater)
                }
            }
        }
    }

    fn grevlex(&self, other: &Self) -> std::cmp::Ordering {
        self.degree().cmp(&other.degree()).then(self.revlex(other))
    }

    fn concat(&self, other: &Self) -> Self {
        match self {
            CrMon::Unit => other.clone(),
            CrMon::Mult(pw, m) => CrMon::Mult(pw.clone(), Box::new(m.concat(other))),
        }
    }

    fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (m, CrMon::Unit) => m.clone(),
            (CrMon::Unit, m) => m.clone(),
            (CrMon::Mult(pw1, m1), CrMon::Mult(pw2, m2)) => {
                if Self::var_lt(pw1, pw2) {
                    CrMon::Mult(pw1.clone(), Box::new(m1.mul(other)))
                } else if Self::var_lt(pw2, pw1) {
                    CrMon::Mult(pw2.clone(), Box::new(self.mul(m2)))
                } else {
                    CrMon::Mult(
                        CrPower {
                            x: pw1.x.clone(),
                            k: &pw1.k + &pw2.k,
                        },
                        Box::new(m1.mul(m2)),
                    )
                }
            }
        }
    }

    fn beq(&self, other: &Self) -> bool {
        self == other
    }
}

/// Closed `Lean.Grind.CommRing.Poly`: decreasing `grevlex`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CrPoly {
    Num(BigInt),
    Add(BigInt, CrMon, Box<CrPoly>),
}

impl CrPoly {
    fn of_mon(m: CrMon) -> Self {
        CrPoly::Add(BigInt::from(1), m, Box::new(CrPoly::Num(BigInt::from(0))))
    }

    fn of_var(x: BigUint) -> Self {
        Self::of_mon(CrMon::of_var(x))
    }

    fn add_const(&self, k: &BigInt) -> Self {
        if k.sign() == Sign::NoSign {
            return self.clone();
        }
        match self {
            CrPoly::Num(c) => CrPoly::Num(c + k),
            CrPoly::Add(a, m, p) => CrPoly::Add(a.clone(), m.clone(), Box::new(p.add_const(k))),
        }
    }

    fn mul_const(&self, k: &BigInt) -> Self {
        if k.sign() == Sign::NoSign {
            return CrPoly::Num(BigInt::from(0));
        }
        if k == &BigInt::from(1) {
            return self.clone();
        }
        match self {
            CrPoly::Num(c) => CrPoly::Num(k * c),
            CrPoly::Add(a, m, p) => CrPoly::Add(k * a, m.clone(), Box::new(p.mul_const(k))),
        }
    }

    fn insert(&self, k: &BigInt, m: &CrMon) -> Self {
        if k.sign() == Sign::NoSign {
            return self.clone();
        }
        if matches!(m, CrMon::Unit) {
            return self.add_const(k);
        }
        self.insert_go(k, m)
    }

    fn insert_go(&self, k: &BigInt, m: &CrMon) -> Self {
        match self {
            CrPoly::Num(c) => CrPoly::Add(k.clone(), m.clone(), Box::new(CrPoly::Num(c.clone()))),
            CrPoly::Add(k2, m2, p) => match m.grevlex(m2) {
                std::cmp::Ordering::Equal => {
                    let s = k + k2;
                    if s.sign() == Sign::NoSign {
                        (**p).clone()
                    } else {
                        CrPoly::Add(s, m.clone(), p.clone())
                    }
                }
                std::cmp::Ordering::Greater => {
                    CrPoly::Add(k.clone(), m.clone(), Box::new(self.clone()))
                }
                std::cmp::Ordering::Less => {
                    CrPoly::Add(k2.clone(), m2.clone(), Box::new(p.insert_go(k, m)))
                }
            },
        }
    }

    fn concat(&self, other: &Self) -> Self {
        match self {
            CrPoly::Num(k) => other.add_const(k),
            CrPoly::Add(k, m, p) => CrPoly::Add(k.clone(), m.clone(), Box::new(p.concat(other))),
        }
    }

    fn combine(p1: &Self, p2: &Self) -> Self {
        match (p1, p2) {
            (CrPoly::Num(k1), CrPoly::Num(k2)) => CrPoly::Num(k1 + k2),
            (CrPoly::Num(k1), CrPoly::Add(..)) => p2.add_const(k1),
            (CrPoly::Add(..), CrPoly::Num(k2)) => p1.add_const(k2),
            (CrPoly::Add(k1, m1, r1), CrPoly::Add(k2, m2, r2)) => match m1.grevlex(m2) {
                std::cmp::Ordering::Equal => {
                    let k = k1 + k2;
                    let rest = Self::combine(r1, r2);
                    if k.sign() == Sign::NoSign {
                        rest
                    } else {
                        CrPoly::Add(k, m1.clone(), Box::new(rest))
                    }
                }
                std::cmp::Ordering::Greater => {
                    CrPoly::Add(k1.clone(), m1.clone(), Box::new(Self::combine(r1, p2)))
                }
                std::cmp::Ordering::Less => {
                    CrPoly::Add(k2.clone(), m2.clone(), Box::new(Self::combine(p1, r2)))
                }
            },
        }
    }

    fn mul_mon(&self, k: &BigInt, m: &CrMon) -> Self {
        if k.sign() == Sign::NoSign {
            return CrPoly::Num(BigInt::from(0));
        }
        if matches!(m, CrMon::Unit) {
            return self.mul_const(k);
        }
        match self {
            CrPoly::Num(c) => {
                if c.sign() == Sign::NoSign {
                    CrPoly::Num(BigInt::from(0))
                } else {
                    CrPoly::Add(k * c, m.clone(), Box::new(CrPoly::Num(BigInt::from(0))))
                }
            }
            CrPoly::Add(c, m2, p) => CrPoly::Add(k * c, m.mul(m2), Box::new(p.mul_mon(k, m))),
        }
    }

    fn mul(&self, other: &Self) -> Self {
        self.mul_go(other, &CrPoly::Num(BigInt::from(0)))
    }

    fn mul_go(&self, other: &Self, acc: &Self) -> Self {
        match self {
            CrPoly::Num(k) => Self::combine(acc, &other.mul_const(k)),
            CrPoly::Add(k, m, p) => p.mul_go(other, &Self::combine(acc, &other.mul_mon(k, m))),
        }
    }

    fn pow(&self, k: &BigUint) -> Option<Self> {
        if *k == BigUint::from(0u32) {
            return Some(CrPoly::Num(BigInt::from(1)));
        }
        if *k == BigUint::from(1u32) {
            return Some(self.clone());
        }
        if k.bits() > 16 {
            return None;
        }
        let km1 = k - 1u32;
        let rec = self.pow(&km1)?;
        Some(self.mul(&rec))
    }

    fn beq(&self, other: &Self) -> bool {
        match (self, other) {
            (CrPoly::Num(a), CrPoly::Num(b)) => a == b,
            (CrPoly::Add(k1, m1, p1), CrPoly::Add(k2, m2, p2)) => {
                k1 == k2 && m1.beq(m2) && p1.beq(p2)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
enum CrExpr {
    Num(BigInt),
    NatCast(BigUint),
    IntCast(BigInt),
    Var(BigUint),
    Neg(Box<CrExpr>),
    Add(Box<CrExpr>, Box<CrExpr>),
    Sub(Box<CrExpr>, Box<CrExpr>),
    Mul(Box<CrExpr>, Box<CrExpr>),
    Pow(Box<CrExpr>, BigUint),
}

impl CrExpr {
    fn to_poly(&self) -> Option<CrPoly> {
        match self {
            CrExpr::Num(k) | CrExpr::IntCast(k) => Some(CrPoly::Num(k.clone())),
            CrExpr::NatCast(k) => Some(CrPoly::Num(BigInt::from(k.clone()))),
            CrExpr::Var(x) => Some(CrPoly::of_var(x.clone())),
            CrExpr::Add(a, b) => Some(CrPoly::combine(&a.to_poly()?, &b.to_poly()?)),
            CrExpr::Mul(a, b) => Some(a.to_poly()?.mul(&b.to_poly()?)),
            CrExpr::Neg(a) => Some(a.to_poly()?.mul_const(&BigInt::from(-1))),
            CrExpr::Sub(a, b) => {
                let pb = b.to_poly()?.mul_const(&BigInt::from(-1));
                Some(CrPoly::combine(&a.to_poly()?, &pb))
            }
            CrExpr::Pow(a, k) => {
                if *k == BigUint::from(0u32) {
                    return Some(CrPoly::Num(BigInt::from(1)));
                }
                match a.as_ref() {
                    CrExpr::Num(n) | CrExpr::IntCast(n) => Some(CrPoly::Num(int_pow(n, k)?)),
                    CrExpr::NatCast(n) => {
                        if k.bits() > 16 {
                            return None;
                        }
                        let e = k.to_u32_digits().first().copied().unwrap_or(0);
                        Some(CrPoly::Num(BigInt::from(n.pow(e))))
                    }
                    CrExpr::Var(x) => Some(CrPoly::of_mon(CrMon::of_pow(x.clone(), k.clone()))),
                    _ => a.to_poly()?.pow(k),
                }
            }
        }
    }
}

#[cfg(test)]
mod closed_int_tests {
    use super::*;

    #[test]
    fn ediv_matches_lean_tidy_div() {
        let n = BigInt::from(4294967296u64);
        let k = BigInt::from(64);
        assert_eq!(int_ediv(&-&n, &k), -BigInt::from(67108864));
        assert_eq!(-int_ediv(&-&n, &k), BigInt::from(67108864));
        assert_eq!(int_ediv(&n, &k), BigInt::from(67108864));
        assert_eq!(
            int_ediv(&BigInt::from(-12), &BigInt::from(7)),
            BigInt::from(-2)
        );
        assert_eq!(
            int_ediv(&BigInt::from(12), &BigInt::from(-7)),
            BigInt::from(-1)
        );
        assert_eq!(
            int_ediv(&BigInt::from(12), &BigInt::from(0)),
            BigInt::from(0)
        );
    }

    #[test]
    fn pow_matches_lean_int_pow() {
        assert_eq!(
            int_pow(&BigInt::from(2), &BigUint::from(63u32)).unwrap(),
            BigInt::from(1u64) << 63
        );
        assert_eq!(
            int_pow(&BigInt::from(-2), &BigUint::from(3u32)).unwrap(),
            BigInt::from(-8)
        );
        assert_eq!(
            int_pow(&BigInt::from(-2), &BigUint::from(4u32)).unwrap(),
            BigInt::from(16)
        );
        assert_eq!(
            int_pow(&BigInt::from(5), &BigUint::from(0u32)).unwrap(),
            BigInt::from(1)
        );
    }

    #[test]
    fn bmod_two_pow_31_is_min_int32() {
        let p31 = BigInt::from(1u64) << 31;
        let p32 = BigUint::from(1u64) << 32;
        assert_eq!(int_bmod(&p31, &p32), -p31);
        assert_eq!(
            int_emod_nat(&BigInt::from(-5), &BigUint::from(3u32)),
            BigInt::from(1)
        );
    }

    #[test]
    fn gcd_64_then_0() {
        assert_eq!(
            num_bigint_gcd(&BigUint::from(64u32), &BigUint::from(0u32)),
            BigUint::from(64u32)
        );
    }

    #[test]
    fn tidy_int64_add_omega_payload() {
        // `#20467`: lo=-(2^63-1), hi=2^64-1, coeffs=[0,0,-2^64,2^64]
        // positivize then div-by-2^64 → (0,0) and [0,0,1,-1].
        let p63: BigInt = BigInt::from(1u64) << 63;
        let p64: BigInt = BigInt::from(1u128) << 64;
        let lo: BigInt = BigInt::from(1) - &p63;
        let hi: BigInt = &p64 - BigInt::from(1);
        let leading: BigInt = -&p64;
        assert!(leading.sign() == Sign::Minus);
        let lo2 = -hi.clone();
        let hi2 = -lo.clone();
        let coeffs = vec![BigInt::from(0), BigInt::from(0), p64.clone(), -p64.clone()];
        let g = p64.magnitude().clone();
        let gk = BigInt::from(g);
        let lo3 = -int_ediv(&(-&lo2), &gk);
        let hi3 = int_ediv(&hi2, &gk);
        assert_eq!(lo3, BigInt::from(0));
        assert_eq!(hi3, BigInt::from(0));
        let out: Vec<_> = coeffs.iter().map(|x| int_ediv(x, &gk)).collect();
        assert_eq!(
            out,
            vec![
                BigInt::from(0),
                BigInt::from(0),
                BigInt::from(1),
                BigInt::from(-1)
            ]
        );
    }

    #[test]
    fn combine_mul_k_cancels_diseq_subst_payload() {
        // Init #17742: diseq_eq_subst_cert 1 p p (num 0) with
        // p = add -1 1 (add 1 0 (num 0)) needs combine_mul_k(-1, 1, p, p) = num 0.
        let p = LinearPoly::Add(
            BigInt::from(-1),
            BigUint::from(1u32),
            Box::new(LinearPoly::Add(
                BigInt::from(1),
                BigUint::from(0u32),
                Box::new(LinearPoly::Num(BigInt::from(0))),
            )),
        );
        let a = p.coeff(&BigUint::from(1u32));
        let b = p.coeff(&BigUint::from(1u32));
        assert_eq!(a, BigInt::from(-1));
        let r = LinearPoly::combine_mul_k(&b, &(-&a), &p, &p);
        assert_eq!(r, LinearPoly::Num(BigInt::from(0)));
        assert!(a.sign() != Sign::NoSign && LinearPoly::Num(BigInt::from(0)).beq(&r));
    }

    #[test]
    fn commring_norm_cnstr_char_ordinal_payload() {
        // Init #17755: norm_cnstr_cert (num 2^32) (var 0) (num 0)
        //   (add (var 0) (intCast (-2^32)))
        let p32: BigInt = BigInt::from(1u64) << 32;
        let lhs = CrExpr::Num(p32.clone());
        let rhs = CrExpr::Var(BigUint::from(0u32));
        let lhs2 = CrExpr::Num(BigInt::from(0));
        let rhs2 = CrExpr::Add(
            Box::new(CrExpr::Var(BigUint::from(0u32))),
            Box::new(CrExpr::IntCast(-p32)),
        );
        let a = CrExpr::Sub(Box::new(rhs), Box::new(lhs)).to_poly().unwrap();
        let b = CrExpr::Sub(Box::new(rhs2), Box::new(lhs2))
            .to_poly()
            .unwrap();
        assert!(a.beq(&b), "{a:?} vs {b:?}");
    }

    #[test]
    fn linear_norm_eq_cert_char_ordinal_payload() {
        // Init #17844: (var 0 + -(2^32-1)) - 0  norms to  1·x0 + (-(2^32-1))
        let k: BigInt = (BigInt::from(1u64) << 32) - 1;
        let lhs = LinearExpr::Add(
            Box::new(LinearExpr::Var(BigUint::from(0u32))),
            Box::new(LinearExpr::Neg(Box::new(LinearExpr::Num(k.clone())))),
        );
        let rhs = LinearExpr::Num(BigInt::from(0));
        let want = LinearPoly::Add(
            BigInt::from(1),
            BigUint::from(0u32),
            Box::new(LinearPoly::Num(-k)),
        );
        let got = LinearExpr::Sub(Box::new(lhs), Box::new(rhs)).norm();
        assert!(want.beq(&got), "{want:?} vs {got:?}");
    }
}

fn num_bigint_gcd(a: &BigUint, b: &BigUint) -> BigUint {
    let mut x = a.clone();
    let mut y = b.clone();
    while y != BigUint::from(0u32) {
        let r = &x % &y;
        x = y;
        y = r;
    }
    x
}
fn decline<T>(msg: impl Into<String>) -> R<T> {
    Err(TcError::Decline(msg.into()))
}

pub struct Checker<'e> {
    pub env: &'e Environment,
    pub names: &'e [std::rc::Rc<String>],
    pub nat_ref: Option<u32>,
    pub string_ref: Option<u32>,
    whnf_cache: RefCell<FxHashMap<usize, Expr>>,
    whnf_core_cache: RefCell<FxHashMap<usize, Expr>>,
    defeq_cache: RefCell<FxHashMap<(u64, usize, usize), bool>>,
    /// `(const name, levels)` to unfolded value, memoized like the C++ kernel's
    /// `m_unfold`. The delta path can unfold the same def/theorem at the same
    /// levels over and over; re-instantiating a large body each time (O(size)
    /// `instantiate_level_params`) is what made `_proof_1_1` blow up.
    unfold_cache: RefCell<FxHashMap<(u32, Vec<Level>), Expr>>,
    /// `(context id, term)` to inferred type. Unlike the caches above this one
    /// works under binders, which is where the redundancy actually is: a term
    /// shared by the DAG is otherwise re-inferred once per occurrence, so a
    /// term applied to two identical arguments doubles the work at every level.
    infer_cache: RefCell<FxHashMap<(u64, usize), Expr>>,
    /// Consts whose telescope has a Prop-inductive binder (`USquash`, `Eq`).
    /// Only those spines need `defeq_args`; everything else stays pairwise.
    proof_arg_cache: RefCell<FxHashMap<u32, bool>>,
    /// Consecutive `Nat.rec` peels of one `bits() >= 20` literal countdown.
    fuel_nat_peels: std::cell::Cell<u32>,
    /// Last bits≥20 literal peeled; used to detect one hugeFuel countdown.
    fuel_nat_last: std::cell::RefCell<Option<num_bigint::BigUint>>,
    /// Lean `infer_only`: skip app-arg checks. Used from PI so we do not
    /// Check a 100k-node proof just to read its type.
    infer_only: std::cell::Cell<bool>,
    /// Tree size of the decl value currently being checked (0 = none).
    /// Eager Regular unfold is budgeted against this, not a library name.
    decl_value_size: std::cell::Cell<u32>,
    /// Theorem type is a 1-ctor 0-index Prop inductive with ≥5 params and
    /// ≥2 ctor fields (class-like; not `Eq` with indices, not a 1-field Prop).
    checking_prop_structure: std::cell::Cell<bool>,
    /// Largest Def body appearing as a head on an equality-shaped type
    /// (1 ctor, indices > 0, Prop). Small equation lemmas of a large Regular
    /// need that Regular to unfold; the lemma name is not tested.
    eq_side_def_size: std::cell::Cell<u32>,
    /// Theorem type is a 1-ctor 0-index Prop that is *not* the multi-arg
    /// class shape. Those instances need a higher Regular cap than huge
    /// proof bodies of similar size.
    checking_simple_prop_inductive: std::cell::Cell<bool>,
    /// Theorem (not def) whose value is ≥10k nodes. Eager Regular cap stays
    /// below circuit size; defs of similar size still unfold helpers.
    checking_large_theorem: std::cell::Cell<bool>,
    /// Defs on an equality-shaped type (and nested Defs mentioned in
    /// those bodies). Unfolded regardless of the size cap so small eq
    /// lemmas of a large aux def still reduce.
    eq_related_defs: RefCell<Vec<u32>>,
}

thread_local! {
    /// Maps `(parent id, pushed type)` to the id of the extended context, so
    /// that two contexts built from the same sequence of types share an id.
    static CTX_IDS: RefCell<FxHashMap<(u64, usize), u64>> = RefCell::new(FxHashMap::default());
    static CTX_NEXT: std::cell::Cell<u64> = const { std::cell::Cell::new(1) };
}

/// `ctx[len-1-i]` is the raw (unshifted) type recorded for bvar `i`.
///
/// The `id` is what makes a type-inference cache possible. Keying on depth
/// alone would be unsound — two contexts of equal length bind different types
/// — so each context carries an identity interned from the sequence of types
/// that built it. Equal ids therefore imply equal contexts; distinct ids for
/// equal contexts would only cost a cache miss, and interning rules that out.
#[derive(Clone, Default)]
struct Ctx {
    /// Invariant: only ever extended through `push`, which keeps `id` in step.
    /// Mutating this directly would leave `id` describing a different context
    /// than `tys` holds, and the inference cache would then hand back a type
    /// inferred under other bindings — a false accept, silently.
    tys: Vec<Expr>,
    id: u64,
}

impl Ctx {
    fn new() -> Self {
        Ctx::default()
    }

    fn push(&mut self, ty: Expr) {
        let key = (self.id, Rc::as_ptr(&ty) as usize);
        self.id = CTX_IDS.with(|m| {
            *m.borrow_mut().entry(key).or_insert_with(|| {
                CTX_NEXT.with(|c| {
                    let v = c.get();
                    c.set(v + 1);
                    v
                })
            })
        });
        self.tys.push(ty);
    }

    fn len(&self) -> usize {
        self.tys.len()
    }

    fn is_empty(&self) -> bool {
        self.tys.is_empty()
    }
}

impl std::ops::Index<usize> for Ctx {
    type Output = Expr;
    fn index(&self, i: usize) -> &Expr {
        &self.tys[i]
    }
}

pub(crate) fn expr_size_capped(e: &Expr, cap: u32) -> u32 {
    let mut n = 0u32;
    let mut stack = vec![e.clone()];
    while let Some(x) = stack.pop() {
        n += 1;
        if n >= cap {
            return cap;
        }
        match &**x {
            ExprData::App(f, a) => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                stack.push(t.clone());
                stack.push(b.clone());
            }
            ExprData::Let(t, v, b) => {
                stack.push(t.clone());
                stack.push(v.clone());
                stack.push(b.clone());
            }
            ExprData::Proj(_, _, v) => stack.push(v.clone()),
            _ => {}
        }
    }
    n
}

fn local_ty(ctx: &Ctx, i: u32) -> Option<Expr> {
    let n = ctx.len();
    if (i as usize) >= n {
        return None;
    }
    let raw = &ctx[n - 1 - i as usize];
    Some(expr::shift(raw, i as i32 + 1, 0))
}

impl<'e> Checker<'e> {
    pub fn new(
        env: &'e Environment,
        names: &'e [std::rc::Rc<String>],
        nat_ref: Option<u32>,
        string_ref: Option<u32>,
    ) -> Self {
        Checker {
            env,
            names,
            nat_ref,
            string_ref,
            whnf_cache: RefCell::new(FxHashMap::default()),
            whnf_core_cache: RefCell::new(FxHashMap::default()),
            defeq_cache: RefCell::new(FxHashMap::default()),
            infer_cache: RefCell::new(FxHashMap::default()),
            proof_arg_cache: RefCell::new(FxHashMap::default()),
            unfold_cache: RefCell::new(FxHashMap::default()),
            fuel_nat_peels: std::cell::Cell::new(0),
            fuel_nat_last: std::cell::RefCell::new(None),
            infer_only: std::cell::Cell::new(false),
            decl_value_size: std::cell::Cell::new(0),
            checking_prop_structure: std::cell::Cell::new(false),
            eq_side_def_size: std::cell::Cell::new(0),
            checking_simple_prop_inductive: std::cell::Cell::new(false),
            checking_large_theorem: std::cell::Cell::new(false),
            eq_related_defs: RefCell::new(Vec::new()),
        }
    }

    fn ptr_key(e: &Expr) -> usize {
        Rc::as_ptr(e) as usize
    }

    fn cacheable(_ctx: &Ctx, _e: &Expr) -> bool {
        // The whnf stack is context-pure: whnf/whnf_core/whnf_major never
        // infer types (try_iota/try_quot/try_nat_extension/try_dite and
        // reduce_nat_arg are all pure reduction over the expression and the
        // environment), so a de Bruijn term's whnf is the same term in every
        // context. Pointer identity is structural identity through the
        // interner, so a ptr-keyed cache is sound under binders as well.
        // (is_def_eq is NOT context-pure — proof irrelevance infers types —
        // and keeps its own stricter gate.) Requiring closed terms in an
        // empty context meant the caches were dead inside declaration
        // bodies, which is where reduction actually happens.
        true
    }

    fn name_str(&self, n: u32) -> &str {
        self.names
            .get(n as usize)
            .map(|s| s.as_str())
            .filter(|s| !s.is_empty())
            .unwrap_or("?")
    }

    fn pp(&self, e: &Expr) -> String {
        self.pp_budget(e, Self::pp_default_budget())
    }

    /// The printer elides once it runs out of budget, which is fine for a
    /// rejection message and misleading when diffing two terms. Raise it with
    /// `KIOTA_PP_BUDGET` when the elision is hiding the difference.
    fn pp_default_budget() -> i32 {
        std::env::var("KIOTA_PP_BUDGET")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(24)
    }

    fn pp_budget(&self, e: &Expr, budget: i32) -> String {
        if budget <= 0 {
            return "…".into();
        }
        match &***e {
            ExprData::BVar(i) => format!("#{i}"),
            ExprData::Sort(l) => format!("Sort({})", level::pp(l)),
            ExprData::Const(n, us) => {
                if us.is_empty() {
                    self.name_str(*n).to_string()
                } else {
                    let ls: Vec<String> = us.iter().map(level::pp).collect();
                    format!("{} .{{{}}}", self.name_str(*n), ls.join(","))
                }
            }
            ExprData::App(_, _) => {
                let (h, args) = expr::unfold_apps(e);
                let mut s = self.pp_budget(&h, budget - 1);
                for a in args {
                    s.push(' ');
                    let inner = self.pp_budget(&a, budget - 1);
                    if inner.contains(' ') {
                        s.push('(');
                        s.push_str(&inner);
                        s.push(')');
                    } else {
                        s.push_str(&inner);
                    }
                }
                s
            }
            ExprData::Lam(_, ty, body) => {
                format!(
                    "(λ {}. {})",
                    self.pp_budget(ty, budget - 1),
                    self.pp_budget(body, budget - 1)
                )
            }
            ExprData::Pi(_, ty, body) => {
                format!(
                    "(Π {}. {})",
                    self.pp_budget(ty, budget - 1),
                    self.pp_budget(body, budget - 1)
                )
            }
            ExprData::Let(ty, val, body) => format!(
                "(let {} := {}; {})",
                self.pp_budget(ty, budget - 1),
                self.pp_budget(val, budget - 1),
                self.pp_budget(body, budget - 1)
            ),
            ExprData::Proj(s, i, v) => format!(
                "{}.{}[{}]",
                self.pp_budget(v, budget - 1),
                i,
                self.name_str(*s)
            ),
            ExprData::Lit(Lit::Nat(n)) => n.to_string(),
            ExprData::Lit(Lit::Str(s)) => format!("{s:?}"),
        }
    }

    pub fn check_decl(&self, name: u32, kind: &str) -> R<()> {
        let ci = self
            .env
            .get(name)
            .ok_or_else(|| TcError::Other(format!("missing const {name}")))?;
        crate::stats::set_theorem_delta_scope(self.name_str(name));
        if std::env::var_os("KIOTA_DEBUG").is_some() && self.name_str(name).contains("_mutual") {
            eprintln!("CHECKING {}", self.name_str(name));
            let _ = std::io::Write::flush(&mut std::io::stderr());
        }
        self.fuel_nat_peels.set(0);
        *self.fuel_nat_last.borrow_mut() = None;
        self.decl_value_size.set(
            ci.value()
                .map(|v| expr_size_capped(v, 200_000))
                .unwrap_or(0),
        );
        self.checking_large_theorem
            .set(kind == "theorem" && self.decl_value_size.get() >= 10_000);
        let multi = kind == "theorem" && self.type_is_multiarg_prop_structure(ci.typ());
        self.checking_prop_structure.set(multi);
        self.checking_simple_prop_inductive
            .set(kind == "theorem" && !multi && self.type_is_unit_ctor_zero_index_prop(ci.typ()));
        {
            let mut rel = self.eq_related_defs.borrow_mut();
            rel.clear();
            if kind == "theorem" {
                self.fill_eq_related_defs(ci.typ(), &mut rel);
            }
            self.eq_side_def_size.set(
                rel.iter()
                    .copied()
                    .map(|n| match self.env.get(n) {
                        Some(ConstantInfo::Def { value, .. }) => expr_size_capped(value, 200_000),
                        _ => 0,
                    })
                    .max()
                    .unwrap_or(0),
            );
        }
        if std::env::var_os("KIOTA_CAP_LOG").is_some() {
            let cur = self.decl_value_size.get();
            let prop = self.checking_prop_structure.get();
            let eq = self.eq_side_def_size.get();
            eprintln!(
                "CAP {} prop={prop} eq={eq} cur={cur} {}",
                kind,
                self.name_str(name)
            );
        }
        // Pointer-keyed WHNF/defeq/infer caches are only useful inside one
        // declaration. Keeping them across decls is how `#3491`–`#3495`
        // grew from ~0.9 GB to multi-GB before the next omega proof.
        // `unfold_cache` is keyed by (const, levels) and is reused.
        self.whnf_cache.borrow_mut().clear();
        self.whnf_core_cache.borrow_mut().clear();
        self.defeq_cache.borrow_mut().clear();
        self.infer_cache.borrow_mut().clear();
        if std::env::var_os("KIOTA_TRACE_DECL").is_some() {
            eprintln!("DECL {kind} {}", self.name_str(name));
        }
        let decl_inst0 = crate::stats::inst_nodes();
        let decl_whnf0 = crate::stats::whnf_calls();
        // Native quot/inductive/ctor/rec kinds are validated elsewhere.
        let level_params = ci.level_params();
        {
            let mut seen: Vec<u32> = Vec::new();
            for p in level_params {
                if seen.contains(p) {
                    return reject(format!("{kind} {name}: duplicate universe parameter"));
                }
                seen.push(*p);
            }
        }
        let typ = ci.typ();
        let ctx: Ctx = Ctx::new();
        let sort = self.infer_type(&ctx, typ)?;
        let lvl = self.ensure_sort(&ctx, &sort)?;
        if kind == "theorem" && !level::is_def_eq(&lvl, &level::zero()) {
            return reject(format!("{kind} {name}: theorem type is not a Prop"));
        }
        let name_s = self.name_str(name);
        crate::stats::set_verbose_target(&name_s);
        crate::stats::set_theorem_delta_scope(&name_s);
        if std::env::var_os("KIOTA_DEBUG").is_some() {
            if let Some(v) = ci.value() {
                let n = expr_size_capped(v, 100_000);
                let nm = self.name_str(name);
                if n >= 10_000 || nm.contains("_mutual") {
                    eprintln!("DECLSIZE {nm} value_nodes~{n}");
                }
            }
        }
        if let Some(value) = ci.value() {
            // Large theorem bodies: infer with Lean infer_only (skip app-arg
            // Check). Small equation lemmas still full-Check. Size, not a
            // library name.
            let vt = if kind == "theorem" && self.decl_value_size.get() >= 10_000 {
                self.with_infer_only(|| self.infer_type(&ctx, value))?
            } else {
                self.infer_type(&ctx, value)?
            };
            if !self.is_def_eq(&ctx, &vt, typ)? {
                if std::env::var_os("KIOTA_DEBUG").is_some() {
                    return reject(format!(
                        "{kind} {name}: value type does not match declared type\n  got:      {}\n  expected: {}\n  got_whnf: {}\n  exp_whnf: {}",
                        self.pp_budget(&vt, 40),
                        self.pp_budget(typ, 40),
                        self.pp_budget(&self.whnf(&ctx, &vt).unwrap_or_else(|_| vt.clone()), 40),
                        self.pp_budget(&self.whnf(&ctx, typ).unwrap_or_else(|_| typ.clone()), 40),
                    ));
                }
                return reject(format!(
                    "{kind} {name}: value type does not match declared type"
                ));
            }
        }
        if std::env::var_os("KIOTA_DECL_STATS").is_some() {
            let di = crate::stats::inst_nodes() - decl_inst0;
            let dw = crate::stats::whnf_calls() - decl_whnf0;
            if di > 100_000 || dw > 1_000_000 {
                eprintln!(
                    "DECLSTATS {} inst=+{} whnf=+{}",
                    self.name_str(name),
                    di,
                    dw
                );
            }
        }
        Ok(())
    }

    // ---------------- Universe / sort helpers ----------------

    /// WHNF with size/hint eager-delta, then one unfold of a large Regular
    /// *type* (value is already Pi/Sort). Circuit Regular *values* (Lam/app
    /// spines) stay folded; unfolding those here intern-explodes FullAdder.
    fn reduce_for_ensure(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let w = self.whnf(ctx, e)?;
        match &**w {
            ExprData::Pi(_, _, _) | ExprData::Sort(_) => return Ok(w),
            _ => {}
        }
        let (head, args) = expr::unfold_apps(&w);
        if let ExprData::Const(n, us) = &**head {
            if let Some(unfolded) = self.unfold_def(*n, us)? {
                let type_alias = matches!(&**unfolded, ExprData::Pi(_, _, _) | ExprData::Sort(_));
                if type_alias || self.eager_whnf_unfolds(*n) {
                    let next = expr::apps(unfolded, &args);
                    return self.whnf_core(ctx, &next);
                }
            }
        }
        Ok(w)
    }

    fn ensure_sort(&self, ctx: &Ctx, e: &Expr) -> R<Level> {
        let w = self.reduce_for_ensure(ctx, e)?;
        match &**w {
            ExprData::Sort(l) => Ok(l.clone()),
            _ => reject("expected a sort"),
        }
    }

    fn ensure_pi(&self, ctx: &Ctx, e: &Expr) -> R<(BinderInfo, Expr, Expr)> {
        let w = self.reduce_for_ensure(ctx, e)?;
        match &**w {
            ExprData::Pi(bi, ty, body) => Ok((*bi, ty.clone(), body.clone())),
            _ => reject("expected a function type"),
        }
    }

    // ---------------- Type inference ----------------

    pub fn infer_type(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        crate::stats::infer_call();
        let key = (ctx.id, Self::ptr_key(e));
        if let Some(t) = self.infer_cache.borrow().get(&key) {
            crate::stats::infer_hit();
            return Ok(t.clone());
        }
        let t = self.infer_type_uncached(ctx, e)?;
        self.infer_cache.borrow_mut().insert(key, t.clone());
        Ok(t)
    }

    fn infer_type_uncached(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        match &***e {
            ExprData::BVar(i) => {
                local_ty(ctx, *i).ok_or_else(|| TcError::Other("bvar out of range".into()))
            }
            ExprData::Sort(l) => Ok(expr::sort(level::succ(l.clone()))),
            ExprData::Const(n, us) => self.infer_const(*n, us),
            ExprData::App(f, a) => {
                let ft = self.infer_type(ctx, f)?;
                let (_, dom, body) = self.ensure_pi(ctx, &ft)?;
                // Lean `infer_only` / mathgraph InferOnly: PI only needs the
                // type, not a full Check of every argument. Nested Check of a
                // 100k-node proof intern-OOMs.
                if !self.infer_only.get() {
                    let at = self.infer_type(ctx, a)?;
                    if !self.is_def_eq(ctx, &at, &dom)? {
                        if std::env::var_os("KIOTA_DEBUG").is_some() {
                            let atw = self.whnf(ctx, &at).unwrap_or_else(|_| at.clone());
                            let dw = self.whnf(ctx, &dom).unwrap_or_else(|_| dom.clone());
                            return reject(format!(
                                "application argument type mismatch\n  got:      {}\n  expected: {}\n  got_whnf: {}\n  exp_whnf: {}\n  fun:      {}\n  arg:      {}",
                                self.pp(&at),
                                self.pp(&dom),
                                self.pp(&atw),
                                self.pp(&dw),
                                self.pp(f),
                                self.pp(a),
                            ));
                        }
                        return reject("application argument type mismatch");
                    }
                }
                Ok(expr::instantiate1(&body, a))
            }
            ExprData::Lam(bi, ty, body) => {
                let tt = self.infer_type(ctx, ty)?;
                self.ensure_sort(ctx, &tt)?;
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(ty.clone());
                let bt = self.infer_type(&ctx2, body)?;
                Ok(expr::pi(*bi, ty.clone(), bt))
            }
            ExprData::Pi(_bi, ty, body) => {
                let tt = self.infer_type(ctx, ty)?;
                let s1 = self.ensure_sort(ctx, &tt)?;
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(ty.clone());
                let bs = self.infer_type(&ctx2, body)?;
                let s2 = self.ensure_sort(&ctx2, &bs)?;
                Ok(expr::sort(level::imax(s1, s2)))
            }
            ExprData::Let(ty, val, body) => {
                let tt = self.infer_type(ctx, ty)?;
                self.ensure_sort(ctx, &tt)?;
                let vt = self.infer_type(ctx, val)?;
                if !self.is_def_eq(ctx, &vt, ty)? {
                    return reject("let value type mismatch");
                }
                let b = expr::instantiate1(body, val);
                self.infer_type(ctx, &b)
            }
            ExprData::Proj(sname, idx, v) => self.infer_proj(ctx, *sname, *idx, v),
            ExprData::Lit(Lit::Nat(_)) => Ok(self.nat_type()?),
            ExprData::Lit(Lit::Str(_)) => Ok(self.string_type()?),
        }
    }

    fn infer_const(&self, n: u32, us: &[Level]) -> R<Expr> {
        let ci = self
            .env
            .get(n)
            .ok_or_else(|| TcError::Other(format!("unknown const {n}")))?;
        let lp = ci.level_params();
        if lp.len() != us.len() {
            return reject("universe param count mismatch");
        }
        let subst = level::subst_map(lp, us);
        Ok(expr::instantiate_level_params(ci.typ(), &subst))
    }

    fn nat_type(&self) -> R<Expr> {
        match self.nat_ref {
            Some(n) => Ok(expr::const_(n, vec![])),
            None => decline("Nat literal used but Nat type unavailable"),
        }
    }
    fn string_type(&self) -> R<Expr> {
        match self.string_ref {
            Some(n) => Ok(expr::const_(n, vec![])),
            None => decline("String literal used but String type unavailable"),
        }
    }

    fn infer_proj(&self, ctx: &Ctx, sname: u32, idx: u32, v: &Expr) -> R<Expr> {
        let vt = self.infer_type(ctx, v)?;
        let vtw = self.whnf(ctx, &vt)?;
        let (head, args) = expr::unfold_apps(&vtw);
        let (ind_name, us) = match &**head {
            ExprData::Const(n, us) => (*n, us.clone()),
            _ => return reject("projection of non-inductive value"),
        };
        if ind_name != sname {
            return reject("projection struct name mismatch");
        }
        let (num_params, ctor_name) = match self.env.get(ind_name) {
            Some(ConstantInfo::InductiveType {
                num_params, ctors, ..
            }) if ctors.len() == 1 => (*num_params, ctors[0]),
            _ => return reject("projection: not a single-constructor inductive"),
        };
        let ctor_ci = match self.env.get(ctor_name) {
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                num_fields,
                ..
            }) => (level_params.clone(), typ.clone(), *num_fields),
            _ => return reject("projection: bad constructor"),
        };
        let (ctor_lp, ctor_typ, num_fields) = ctor_ci;
        if idx >= num_fields {
            return reject("projection index out of range");
        }
        let subst = level::subst_map(&ctor_lp, &us);
        let mut ct = expr::instantiate_level_params(&ctor_typ, &subst);
        // instantiate params
        if (args.len() as u32) < num_params {
            return reject("projection: too few params");
        }
        for p in args.iter().take(num_params as usize) {
            let (_, _dom, body) = self.ensure_pi(ctx, &ct)?;
            ct = expr::instantiate1(&body, p);
        }
        // walk `idx` fields, substituting earlier fields with proj v i
        let mut field_types = Vec::new();
        let mut cur = ct;
        for _ in 0..num_fields {
            let (_, dom, body) = self.ensure_pi(ctx, &cur)?;
            field_types.push(dom.clone());
            cur = body;
            // note body still has a dangling bvar 0 representing this field;
            // we substitute concretely below once we know which projections to build.
            break;
        }
        // Re-derive properly: substitute proj(v,0)..proj(v,idx-1) into the telescope.
        let mut ct2 = {
            let subst2 = level::subst_map(&ctor_lp, &us);
            let mut t = expr::instantiate_level_params(&ctor_typ, &subst2);
            for p in args.iter().take(num_params as usize) {
                let (_, _d, body) = self.ensure_pi(ctx, &t)?;
                t = expr::instantiate1(&body, p);
            }
            t
        };
        for i in 0..idx {
            let (_, _dom, body) = self.ensure_pi(ctx, &ct2)?;
            let proj_i = expr::proj(sname, i, v.clone());
            ct2 = expr::instantiate1(&body, &proj_i);
        }
        let (_, dom, _body) = self.ensure_pi(ctx, &ct2)?;
        if self.is_prop(ctx, &vtw)? {
            if !self.is_prop(ctx, &dom)? {
                return reject("cannot project a Type field from a Prop structure");
            }
        }
        Ok(dom)
    }

    fn occurs_bvar(e: &Expr, i: u32) -> bool {
        match &***e {
            ExprData::BVar(j) => *j == i,
            ExprData::App(f, a) => Self::occurs_bvar(f, i) || Self::occurs_bvar(a, i),
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                Self::occurs_bvar(t, i) || Self::occurs_bvar(b, i + 1)
            }
            ExprData::Let(t, v, b) => {
                Self::occurs_bvar(t, i) || Self::occurs_bvar(v, i) || Self::occurs_bvar(b, i + 1)
            }
            ExprData::Proj(_, _, v) => Self::occurs_bvar(v, i),
            _ => false,
        }
    }

    fn nat_ctors(&self) -> Option<(u32, u32)> {
        let n = self.nat_ref?;
        match self.env.get(n) {
            Some(ConstantInfo::InductiveType { ctors, .. }) if ctors.len() == 2 => {
                Some((ctors[0], ctors[1]))
            }
            _ => None,
        }
    }

    fn is_closed_numeral(l: &Level) -> bool {
        match &**l {
            crate::level::LevelData::Zero => true,
            crate::level::LevelData::Succ(a) => Self::is_closed_numeral(a),
            _ => false,
        }
    }

    fn is_non_rec_structure(&self, name: u32) -> bool {
        matches!(
            self.env.get(name),
            Some(ConstantInfo::InductiveType {
                ctors,
                num_indices,
                is_rec,
                ..
            }) if ctors.len() == 1 && *num_indices == 0 && !*is_rec
        )
    }

    fn structure_num_fields(&self, name: u32) -> Option<u32> {
        match self.env.get(name) {
            Some(ConstantInfo::InductiveType { ctors, .. }) if ctors.len() == 1 => {
                match self.env.get(ctors[0]) {
                    Some(ConstantInfo::Constructor { num_fields, .. }) => Some(*num_fields),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_unit_like_pair(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let ta = match self.infer_type(ctx, a) {
            Ok(t) => t,
            Err(_) => return Ok(false),
        };
        let tb = match self.infer_type(ctx, b) {
            Ok(t) => t,
            Err(_) => return Ok(false),
        };
        if !self.is_def_eq(ctx, &ta, &tb)? {
            return Ok(false);
        }
        let tw = self.whnf(ctx, &ta)?;
        let (head, _) = expr::unfold_apps(&tw);
        match &**head {
            ExprData::Const(n, _) if self.is_non_rec_structure(*n) => {
                Ok(self.structure_num_fields(*n) == Some(0))
            }
            _ => Ok(false),
        }
    }

    fn to_ctor_when_structure(
        &self,
        ctx: &Ctx,
        all: &[u32],
        params: &[Expr],
        major: &Expr,
    ) -> R<Option<(u32, u32, Vec<Expr>)>> {
        if all.len() != 1 {
            return Ok(None);
        }
        let tname = all[0];
        if !self.is_non_rec_structure(tname) {
            return Ok(None);
        }
        let (ctors, num_params) = match self.env.get(tname) {
            Some(ConstantInfo::InductiveType {
                ctors, num_params, ..
            }) => (ctors.clone(), *num_params),
            _ => return Ok(None),
        };
        let cname = ctors[0];
        let nfields = match self.env.get(cname) {
            Some(ConstantInfo::Constructor { num_fields, .. }) => *num_fields,
            _ => return Ok(None),
        };
        let mt = self.infer_type(ctx, major)?;
        let mtw = self.whnf(ctx, &mt)?;
        let (thead, targs) = expr::unfold_apps(&mtw);
        match &**thead {
            ExprData::Const(n, _) if *n == tname => {
                if targs.len() < num_params as usize {
                    return Ok(None);
                }
                let mut ctor_args: Vec<Expr> = targs[..num_params as usize].to_vec();
                for i in 0..nfields {
                    ctor_args.push(expr::proj(tname, i, major.clone()));
                }
                let _ = params;
                Ok(Some((cname, num_params, ctor_args)))
            }
            _ => Ok(None),
        }
    }

    /// `ty` is a Prop, i.e. `infer_type(ty)` is `Sort 0` (up to defeq / imax).
    fn is_prop(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        if let Ok(s) = self.infer_type(ctx, ty) {
            if let Ok(l) = self.ensure_sort(ctx, &s) {
                if level::is_def_eq(&l, &level::zero()) {
                    return Ok(true);
                }
            }
        }
        // Prop-class apps (`Small α`) sometimes infer as a non-zero sort
        // (imax / unused universe param). A *fully applied* inductive whose
        // result sort is `Sort 0` is still a Prop.
        let w = match self.whnf(ctx, ty) {
            Ok(w) => w,
            Err(_) => return Ok(false),
        };
        let (h, args) = expr::unfold_apps(&w);
        let ExprData::Const(n, _) = &**h else {
            return Ok(false);
        };
        let Some(ConstantInfo::InductiveType {
            typ, num_params, ..
        }) = self.env.get(*n)
        else {
            return Ok(false);
        };
        if (args.len() as u32) < *num_params {
            return Ok(false);
        }
        Ok(self.sort_codomain_is_prop(typ))
    }

    fn sort_codomain_is_prop(&self, ty: &Expr) -> bool {
        let mut t = ty.clone();
        loop {
            match &**t {
                ExprData::Pi(_, _, b) => t = b.clone(),
                ExprData::Sort(l) => return level::is_def_eq(l, &level::zero()),
                _ => return false,
            }
        }
    }

    fn const_typ(&self, n: u32) -> Option<&Expr> {
        match self.env.get(n)? {
            ConstantInfo::InductiveType { typ, .. }
            | ConstantInfo::Constructor { typ, .. }
            | ConstantInfo::Recursor { typ, .. }
            | ConstantInfo::Def { typ, .. }
            | ConstantInfo::Theorem { typ, .. }
            | ConstantInfo::Axiom { typ, .. }
            | ConstantInfo::Opaque { typ, .. }
            | ConstantInfo::Quot { typ, .. } => Some(typ),
        }
    }

    /// True when `e` cannot be a proof, so PI must not `infer_type` it.
    /// Large Regular heads are data (not theorems); inferring them as proofs
    /// walks their bodies.
    fn obviously_not_proof(&self, e: &Expr) -> bool {
        match &***e {
            ExprData::Sort(_)
            | ExprData::Pi(_, _, _)
            | ExprData::Lam(_, _, _)
            | ExprData::Lit(_) => true,
            _ => {
                let (h, args) = expr::unfold_apps(e);
                let ExprData::Const(n, _) = &**h else {
                    return false;
                };
                if matches!(self.env.get(*n), Some(ConstantInfo::Def { .. }))
                    && !self.eager_whnf_unfolds(*n)
                {
                    return true;
                }
                match self.env.get(*n) {
                    Some(ConstantInfo::InductiveType {
                        typ, num_params, ..
                    }) if (args.len() as u32) >= *num_params => !self.sort_codomain_is_prop(typ),
                    Some(ConstantInfo::Constructor { induct, .. }) => match self.env.get(*induct) {
                        Some(ConstantInfo::InductiveType { typ, .. }) => {
                            !self.sort_codomain_is_prop(typ)
                        }
                        _ => false,
                    },
                    _ => false,
                }
            }
        }
    }

    /// Domain of a binder is a Prop-valued inductive app (`Small α`, `Eq a b`).
    /// Cheap: no `infer_type`. `Sort 0` as a domain is Prop-the-universe
    /// (the argument is a proposition, not a proof) — do not skip those.
    fn domain_is_prop_inductive(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        let w = match self.whnf(ctx, ty) {
            Ok(w) => w,
            Err(_) => return Ok(false),
        };
        if matches!(&**w, ExprData::Sort(_)) {
            return Ok(false);
        }
        let (h, args) = expr::unfold_apps(&w);
        let ExprData::Const(n, _) = &**h else {
            return Ok(false);
        };
        match self.env.get(*n) {
            Some(ConstantInfo::InductiveType {
                typ, num_params, ..
            }) if (args.len() as u32) >= *num_params => Ok(self.sort_codomain_is_prop(typ)),
            _ => Ok(false),
        }
    }

    fn with_infer_only<T>(&self, f: impl FnOnce() -> T) -> T {
        let old = self.infer_only.replace(true);
        let r = f();
        self.infer_only.set(old);
        r
    }

    fn proofs_of_same_prop(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        if self.obviously_not_proof(a) || self.obviously_not_proof(b) {
            return Ok(false);
        }
        self.with_infer_only(|| self.proofs_of_same_prop_go(ctx, a, b))
    }

    fn proofs_of_same_prop_go(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let ta = match self.infer_type(ctx, a) {
            Ok(t) => t,
            Err(_) => return Ok(false),
        };
        let prop_a = self.is_prop(ctx, &ta)?;
        if !prop_a {
            return Ok(false);
        }
        let tb = match self.infer_type(ctx, b) {
            Ok(t) => t,
            Err(_) => return Ok(false),
        };
        let eq = self.is_def_eq(ctx, &ta, &tb)?;
        if !eq {
            if std::env::var_os("KIOTA_TRACE_PI").is_some() {
                eprintln!(
                    "PI_FAIL ctx={} a={} b={} ta={} tb={}",
                    ctx.len(),
                    self.pp_budget(a, 20),
                    self.pp_budget(b, 20),
                    self.pp_budget(&ta, 40),
                    self.pp_budget(&tb, 40),
                );
            }
        }
        Ok(eq)
    }

    fn const_has_proof_arg(&self, n: u32) -> bool {
        if let Some(&b) = self.proof_arg_cache.borrow().get(&n) {
            return b;
        }
        let b = self.const_has_proof_arg_uncached(n);
        self.proof_arg_cache.borrow_mut().insert(n, b);
        b
    }

    fn const_has_proof_arg_uncached(&self, n: u32) -> bool {
        let Some(ci) = self.env.get(n) else {
            return false;
        };
        let mut t = ci.typ().clone();
        let empty = Ctx::new();
        for _ in 0..64 {
            match &**t {
                ExprData::Pi(_, dom, body) => {
                    if self.domain_is_prop_inductive(&empty, dom).unwrap_or(false) {
                        return true;
                    }
                    t = body.clone();
                }
                _ => match self.whnf(&empty, &t) {
                    Ok(w) if !Rc::ptr_eq(&w, &t) => t = w,
                    _ => return false,
                },
            }
        }
        false
    }

    fn pairwise_args(&self, ctx: &Ctx, a1: &[Expr], a2: &[Expr]) -> R<bool> {
        if a1.len() != a2.len() {
            return Ok(false);
        }
        for (x, y) in a1.iter().zip(a2.iter()) {
            if !self.is_def_eq(ctx, x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Compare argument spines of a common function. Binders whose domain is
    /// a Prop are skipped: any two inhabitants are identified by proof
    /// irrelevance, using the *instantiated telescope domain* rather than
    /// re-inferring the arguments from `ctx`.
    ///
    /// `HetT.ext` is the witness. After `cases x; cases y; cases h`,
    /// `USquash (Subtype P) x.small` vs `USquash (Subtype P) y.small` must
    /// convert. `x.small` / `y.small` are still distinct bvars whose context
    /// types mention the pre-`cases` `Property` fields, so PI-by-infer fails;
    /// the structure telescope's next domain is `Small (Subtype P)` on both
    /// sides, which *is* a Prop.
    fn defeq_args(&self, ctx: &Ctx, fn_ty: &Expr, a1: &[Expr], a2: &[Expr]) -> R<bool> {
        if a1.len() != a2.len() {
            return Ok(false);
        }
        let mut ty = fn_ty.clone();
        let mut i = 0;
        while i < a1.len() {
            let (_, dom, body) = match self.ensure_pi(ctx, &ty) {
                Ok(t) => t,
                Err(_) => {
                    while i < a1.len() {
                        if !self.is_def_eq(ctx, &a1[i], &a2[i])? {
                            return Ok(false);
                        }
                        i += 1;
                    }
                    return Ok(true);
                }
            };
            if self.domain_is_prop_inductive(ctx, &dom)? {
                ty = expr::instantiate1(&body, &a1[i]);
                i += 1;
                continue;
            }
            if !self.is_def_eq(ctx, &a1[i], &a2[i])? {
                return Ok(false);
            }
            ty = expr::instantiate1(&body, &a1[i]);
            i += 1;
        }
        Ok(true)
    }

    // ---------------- Reduction ----------------

    pub fn whnf(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let depth = WHNF_DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        if depth > 2048 {
            WHNF_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            if depth == 2049 && std::env::var_os("KIOTA_DEBUG").is_some() {
                eprintln!("WHNF_DEPTH {}", self.pp_budget(e, 50));
            }
            return Ok(e.clone());
        }
        let r = self.whnf_inner(ctx, e);
        WHNF_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        r
    }

    fn whnf_inner(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        crate::stats::whnf_call();
        let cache = Self::cacheable(ctx, e);
        if cache {
            let k = Self::ptr_key(e);
            if let Some(r) = self.whnf_cache.borrow().get(&k) {
                return Ok(r.clone());
            }
        }
        let mut cur = e.clone();
        let r = loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            if let ExprData::Const(n, us) = &**head {
                if self.eager_whnf_unfolds(*n) {
                    if let Some(unfolded) = self.unfold_def(*n, us)? {
                        let (_, args) = expr::unfold_apps(&core);
                        let next = expr::apps(unfolded, &args);
                        if Rc::ptr_eq(&next, &cur) {
                            break core;
                        }
                        cur = next;
                        continue;
                    }
                }
            }
            break core;
        };
        if cache {
            self.whnf_cache
                .borrow_mut()
                .insert(Self::ptr_key(e), r.clone());
        }
        Ok(r)
    }

    /// Same as `whnf`: small defs unfold, huge Regular defs stay folded.
    fn whnf_for_defeq(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        self.whnf(ctx, e)
    }

    /// Congruence on unreduced matching Proj / same-const apps.
    /// Full WHNF of `f 1 a` vs `f 1 (Acc.intro …)` unfolds `f` and iotas
    /// Acc.rec on only the constructor side. Same WHNF-first path also
    /// iota-peels intern-distinct `s.i` / `Nat.rec` spines (`#3495`, `#4000`).
    /// `false` means "not proved this way", never "not defeq".
    fn try_unreduced_const_congruence(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        match (&***a, &***b) {
            (ExprData::Proj(s1, i1, v1), ExprData::Proj(s2, i2, v2)) if s1 == s2 && i1 == i2 => {
                if self.is_def_eq(ctx, v1, v2)? {
                    return Ok(true);
                }
            }
            _ => {}
        }
        let (h1, a1) = expr::unfold_apps(a);
        let (h2, a2) = expr::unfold_apps(b);
        let (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) = (&**h1, &**h2) else {
            return Ok(false);
        };
        if std::env::var_os("KIOTA_TRACE_LINEAR").is_some() {
            let s1 = self.name_str(*n1);
            let s2 = self.name_str(*n2);
            if (s1 == "Eq" || s1.ends_with(".Eq") || s2 == "Eq" || s2.ends_with(".Eq"))
                && a1.iter().chain(a2.iter()).any(|e| {
                    let p = self.pp_budget(e, 40);
                    p.contains("norm_eq_cert")
                })
            {
                eprintln!(
                    "EQCONG n1={s1}#{n1} n2={s2}#{n2} na={} nb={} us={} vs={} same={}",
                    a1.len(),
                    a2.len(),
                    u1.len(),
                    u2.len(),
                    n1 == n2
                );
            }
        }
        if n1 != n2 || a1.len() != a2.len() || u1.len() != u2.len() {
            return Ok(false);
        }
        if !u1
            .iter()
            .zip(u2.iter())
            .all(|(x, y)| level::is_def_eq(x, y))
        {
            return Ok(false);
        }
        let eq_trace = std::env::var_os("KIOTA_TRACE_LINEAR").is_some()
            && a1
                .iter()
                .chain(a2.iter())
                .any(|e| self.pp_budget(e, 40).contains("norm_eq_cert"));
        let r = if self.const_has_proof_arg(*n1) {
            match self.infer_const(*n1, u1) {
                Ok(fn_ty) => self.defeq_args(ctx, &fn_ty, &a1, &a2)?,
                Err(_) => self.pairwise_args(ctx, &a1, &a2)?,
            }
        } else {
            self.pairwise_args(ctx, &a1, &a2)?
        };
        if eq_trace {
            eprintln!("EQARGS r={r} n={} na={}", self.name_str(*n1), a1.len());
        }
        Ok(r)
    }

    fn is_ctor_or_nat_lit_head(&self, e: &Expr) -> bool {
        let (head, _) = expr::unfold_apps(e);
        match &**head {
            ExprData::Lit(Lit::Nat(_)) => true,
            ExprData::Const(n, _) => {
                matches!(self.env.get(*n), Some(ConstantInfo::Constructor { .. }))
            }
            _ => false,
        }
    }

    /// Acc-shape: Prop inductive, recursive, one constructor. Theorem
    /// wrappers of the major (`_proof_2 := Acc.intro`) must unfold before iota.
    fn recursor_unfolds_thm_major(&self, recursor: u32) -> bool {
        let Some(ConstantInfo::Recursor { all, .. }) = self.env.get(recursor) else {
            return false;
        };
        let Some(&ind) = all.first() else {
            return false;
        };
        match self.env.get(ind) {
            Some(ConstantInfo::InductiveType {
                typ, is_rec, ctors, ..
            }) => *is_rec && ctors.len() == 1 && self.sort_codomain_is_prop(typ),
            _ => false,
        }
    }

    /// Defs always. Recursor majors of a Prop, recursive, 1-ctor inductive
    /// (Acc-shape): beta-only unfold of a theorem wrapper whose value is a
    /// constructor (`redex._proof_2 := Acc.intro`).
    fn whnf_major(&self, ctx: &Ctx, e: &Expr, recursor: u32) -> R<Expr> {
        let thm_major = self.recursor_unfolds_thm_major(recursor);
        let mut cur = e.clone();
        loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            if let ExprData::Const(n, us) = &**head {
                let (_, args) = expr::unfold_apps(&core);
                if let Some(unfolded) = self.unfold_def(*n, us)? {
                    cur = expr::apps(unfolded, &args);
                    continue;
                }
                if thm_major {
                    if let Some(unfolded) = self.unfold_delta(*n, us, true)? {
                        let mut body = unfolded;
                        let mut i = 0;
                        while i < args.len() {
                            if let ExprData::Lam(_, _, b) = &**body {
                                body = expr::instantiate1(b, &args[i]);
                                i += 1;
                            } else {
                                break;
                            }
                        }
                        let next = expr::apps(body, &args[i..]);
                        if self.is_ctor_or_nat_lit_head(&next) {
                            cur = next;
                            continue;
                        }
                    }
                }
            }
            return Ok(core);
        }
    }

    /// beta/zeta/proj/iota reduction to whnf, WITHOUT unfolding delta.
    fn whnf_core(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let cache = Self::cacheable(ctx, e);
        if cache {
            let k = Self::ptr_key(e);
            if let Some(r) = self.whnf_core_cache.borrow().get(&k) {
                return Ok(r.clone());
            }
        }
        let r = self.whnf_core_go(ctx, e)?;
        if cache {
            self.whnf_core_cache
                .borrow_mut()
                .insert(Self::ptr_key(e), r.clone());
        }
        Ok(r)
    }

    fn whnf_core_go(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let mut cur = e.clone();
        loop {
            match &**cur {
                ExprData::App(_, _) => {
                    let (head, args) = expr::unfold_apps(&cur);
                    match &**head {
                        ExprData::Lam(_, _, _) => {
                            let mut body = head.clone();
                            let mut i = 0;
                            while let ExprData::Lam(_, _, b) = &**body.clone() {
                                if i >= args.len() {
                                    break;
                                }
                                body = b.clone();
                                i += 1;
                            }
                            if i == 0 {
                                return Ok(cur);
                            }
                            let consumed = &args[..i];
                            let rest = &args[i..];
                            // instantiate consumed args (reverse order: last-bound first)
                            let mut rev: Vec<Expr> = consumed.to_vec();
                            rev.reverse();
                            let reduced = expr::instantiate(&body, &rev);
                            cur = expr::apps(reduced, rest);
                            continue;
                        }
                        // Class projections: `HAdd.hAdd` / `OfNat.ofNat` unfold to
                        // `s.i` applied to further args; reduce the proj head first.
                        ExprData::Proj(sname, idx, v) => {
                            let vw = self.whnf(ctx, v)?;
                            let (phead, pargs) = expr::unfold_apps(&vw);
                            if let ExprData::Const(cname, _us) = &**phead {
                                if let Some(ConstantInfo::Constructor { num_params, .. }) =
                                    self.env.get(*cname)
                                {
                                    let fi = (*num_params + *idx) as usize;
                                    if fi < pargs.len() {
                                        cur = expr::apps(pargs[fi].clone(), &args);
                                        continue;
                                    }
                                }
                            }
                            if let ExprData::Lit(Lit::Str(s)) = &**vw {
                                if self.name_str(*sname) == "String" && *idx == 0 {
                                    if let Some(ba) = self.string_to_byte_array(s) {
                                        cur = expr::apps(ba, &args);
                                        continue;
                                    }
                                }
                            }
                            if Rc::ptr_eq(&vw, v) {
                                return Ok(cur);
                            }
                            return Ok(expr::apps(expr::proj(*sname, *idx, vw), &args));
                        }
                        _ => {
                            if let Some(r) = self.try_iota(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_quot(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_nat_extension(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_omega_combo(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_omega_constraint(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_intlist(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_int_linear(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_comm_ring(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_rat(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_dite(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            return Ok(cur);
                        }
                    }
                }
                ExprData::Let(_, val, body) => {
                    cur = expr::instantiate1(body, val);
                    continue;
                }
                ExprData::Proj(sname, idx, v) => {
                    let vw = self.whnf(ctx, v)?;
                    let (head, args) = expr::unfold_apps(&vw);
                    if let ExprData::Const(cname, _us) = &**head {
                        if let Some(ConstantInfo::Constructor { num_params, .. }) =
                            self.env.get(*cname)
                        {
                            let fi = (*num_params + *idx) as usize;
                            if fi < args.len() {
                                cur = args[fi].clone();
                                continue;
                            }
                        }
                    }
                    if let ExprData::Lit(Lit::Str(s)) = &**vw {
                        if self.name_str(*sname) == "String" && *idx == 0 {
                            if let Some(ba) = self.string_to_byte_array(s) {
                                cur = ba;
                                continue;
                            }
                        }
                    }
                    if Rc::ptr_eq(&vw, v) {
                        return Ok(cur);
                    }
                    return Ok(expr::proj(*sname, *idx, vw));
                }
                _ => return Ok(cur),
            }
        }
    }

    /// Delta for `whnf`: Defs only. The full `whnf` (used everywhere, hot,
    /// uncached under binders) must NOT unfold theorem values — their proof
    /// terms are huge and instantiating them per call explodes (grind-ring-5
    /// went from 1s to >2min). The is_def_eq delta path below is the cold,
    /// targeted path; it may unfold theorems via `unfold_delta`.
    fn unfold_def(&self, n: u32, us: &[Level]) -> R<Option<Expr>> {
        match self.env.get(n) {
            Some(ConstantInfo::Def {
                level_params,
                value,
                ..
            }) => {
                let key = (n, us.to_vec());
                if let Some(r) = self.unfold_cache.borrow().get(&key) {
                    return Ok(Some(r.clone()));
                }
                let subst = level::subst_map(level_params, us);
                let r = expr::instantiate_level_params(value, &subst);
                self.unfold_cache.borrow_mut().insert(key, r.clone());
                Ok(Some(r))
            }
            Some(ConstantInfo::Opaque { .. }) => Ok(None),
            _ => Ok(None),
        }
    }

    /// Delta for the is_def_eq delta path: Defs AND theorems. Lean's kernel
    /// unfolds any constant with a value (`is_delta` checks only `has_value`),
    /// theorem bodies included — e.g. `Acc.inv` reduces on `Acc.intro`, which
    /// `WellFounded.fixF_eq` needs. Only the cold delta path does this; the
    /// hot `whnf` loop stays Def-only for performance.
    fn unfold_delta(&self, n: u32, us: &[Level], theorems: bool) -> R<Option<Expr>> {
        if let Some(r) = self.unfold_def(n, us)? {
            return Ok(Some(r));
        }
        if !theorems || std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_some() {
            return Ok(None);
        }
        match self.env.get(n) {
            Some(ConstantInfo::Theorem {
                level_params,
                value,
                ..
            }) => {
                let key = (n, us.to_vec());
                if let Some(r) = self.unfold_cache.borrow().get(&key) {
                    return Ok(Some(r.clone()));
                }
                let subst = level::subst_map(level_params, us);
                let r = expr::instantiate_level_params(value, &subst);
                self.unfold_cache.borrow_mut().insert(key, r.clone());
                Ok(Some(r))
            }
            _ => Ok(None),
        }
    }

    fn def_height(&self, n: u32) -> i64 {
        match self.env.get(n) {
            Some(ConstantInfo::Def { hints, .. }) => match hints {
                ReducibilityHints::Opaque => -2,
                ReducibilityHints::Abbrev => i64::MAX - 1,
                ReducibilityHints::Regular(h) => *h as i64,
            },
            Some(ConstantInfo::Theorem { .. }) => -1,
            _ => -2,
        }
    }

    /// Same-head delta only helps unused parameters (`Function.const`).
    /// Instantiating a huge same-head body to discover that is wasted work.
    fn delta_body_is_small(&self, n: u32) -> bool {
        const CAP: u32 = 512;
        self.def_body_under(n, CAP)
    }

    /// Eager WHNF unfolds Abbrev always and Regular/theorem bodies under a
    /// size cap. Medium Regulars (hundreds of nodes) still unfold so linear
    /// cancellation typechecks; circuit-sized Regulars stay folded.
    /// `ensure_pi` may one-step unfold a larger Regular wrapping a Pi.
    /// Class-like Prop: 1 ctor, 0 indices, ≥5 params, ≥2 fields. Equality:
    /// 1 ctor, indices > 0, Prop. 1-field 0-index Prop is the remaining
    /// simple case. No library-name test.
    fn peel_to_inductive_head<'a>(
        &'a self,
        typ: &Expr,
    ) -> Option<(u32, &'a [u32], u32, u32, &'a Expr)> {
        let mut t = typ.clone();
        for _ in 0..64 {
            match &**t {
                ExprData::Pi(_, _, b) => t = b.clone(),
                _ => break,
            }
        }
        let (head, _) = expr::unfold_apps(&t);
        let ExprData::Const(n, _) = &**head else {
            return None;
        };
        match self.env.get(*n) {
            Some(ConstantInfo::InductiveType {
                ctors,
                num_indices,
                num_params,
                typ: ity,
                ..
            }) => Some((*n, ctors.as_slice(), *num_indices, *num_params, ity)),
            _ => None,
        }
    }

    fn type_is_unit_ctor_zero_index_prop(&self, typ: &Expr) -> bool {
        let Some((_, ctors, num_indices, _, ity)) = self.peel_to_inductive_head(typ) else {
            return false;
        };
        ctors.len() == 1 && num_indices == 0 && self.sort_codomain_is_prop(ity)
    }

    fn type_is_multiarg_prop_structure(&self, typ: &Expr) -> bool {
        let Some((_, ctors, num_indices, num_params, ity)) = self.peel_to_inductive_head(typ)
        else {
            return false;
        };
        if ctors.len() != 1 || num_indices != 0 || num_params < 5 {
            return false;
        }
        if !self.sort_codomain_is_prop(ity) {
            return false;
        }
        matches!(
            self.env.get(ctors[0]),
            Some(ConstantInfo::Constructor { num_fields, .. }) if *num_fields >= 2
        )
    }

    /// `Eq`/`HEq` shape: Prop, one ctor, at least one index.
    fn type_is_equality_shaped(&self, typ: &Expr) -> bool {
        let Some((_, ctors, num_indices, _, ity)) = self.peel_to_inductive_head(typ) else {
            return false;
        };
        ctors.len() == 1 && num_indices > 0 && self.sort_codomain_is_prop(ity)
    }

    /// `Eq`/`HEq` shape: Prop, one ctor, at least one index. Collects Def
    /// heads on the equated arguments and Defs mentioned in those bodies
    /// (one level).
    fn fill_eq_related_defs(&self, typ: &Expr, out: &mut Vec<u32>) {
        if !self.type_is_equality_shaped(typ) {
            return;
        }
        self.collect_def_consts(typ, out);
        let first = out.clone();
        for n in &first {
            if let Some(ConstantInfo::Def { value, .. }) = self.env.get(*n) {
                self.collect_def_consts(value, out);
            }
        }
        let second: Vec<u32> = out.iter().copied().filter(|n| !first.contains(n)).collect();
        for n in &second {
            if let Some(ConstantInfo::Def { value, .. }) = self.env.get(*n) {
                self.collect_def_consts(value, out);
            }
        }
    }

    fn collect_def_consts(&self, e: &Expr, out: &mut Vec<u32>) {
        let mut stack = vec![e.clone()];
        let mut steps = 0u32;
        while let Some(x) = stack.pop() {
            steps += 1;
            if steps > 200_000 {
                break;
            }
            match &**x {
                ExprData::Const(n, _) => {
                    if matches!(self.env.get(*n), Some(ConstantInfo::Def { .. }))
                        && !out.contains(n)
                    {
                        out.push(*n);
                    }
                }
                ExprData::App(f, a) => {
                    stack.push(f.clone());
                    stack.push(a.clone());
                }
                ExprData::Lam(_, ty, b) | ExprData::Pi(_, ty, b) => {
                    stack.push(ty.clone());
                    stack.push(b.clone());
                }
                ExprData::Let(ty, v, b) => {
                    stack.push(ty.clone());
                    stack.push(v.clone());
                    stack.push(b.clone());
                }
                ExprData::Proj(_, _, v) => stack.push(v.clone()),
                _ => {}
            }
        }
    }

    fn eager_whnf_unfolds(&self, n: u32) -> bool {
        const CIRCUIT: u32 = 100_000;
        // Cap Regular unfold by the decl being checked. Small proofs must
        // not instantiate 20k+ Regulars (intern explosion). Equality-shaped
        // types boost the cap to the equated Def so small `.eq_1` lemmas of
        // a 40k Regular still reduce. Prop-structure instances stay tighter.
        if self.eq_related_defs.borrow().contains(&n) {
            // Equation lemmas of a large Regular must unfold it. Circuit-sized
            // Regulars intern-explode inside a tiny proof; those wait for a
            // large current decl.
            let related_sz = match self.env.get(n) {
                Some(ConstantInfo::Def { value, .. }) => expr_size_capped(value, CIRCUIT),
                _ => 0,
            };
            if related_sz < 50_000 || self.decl_value_size.get() >= 10_000 {
                return self.def_body_under(n, CIRCUIT);
            }
        }
        let cur = self.decl_value_size.get();
        // Hard ceiling below circuit Regulars (~3k–7k). A huge current proof
        // must not raise the cap and instantiate those; equation lemmas of
        // them unfold via `eq_related_defs` instead.
        const CEILING: u32 = 3_000;
        let cap = if self.checking_prop_structure.get() {
            // Class-like theorems: stay below circuit Regulars (~3k–7k).
            // 512 rejected FullAdder carry; 3000 intern-exploded the out instance.
            2_048
        } else if self.checking_simple_prop_inductive.get() {
            // 1-ctor 0-index Prop instances (not the multi-arg class shape)
            // need iterator-sized Regulars in the 1k–8k band, still below
            // the larger circuit Regulars.
            8_000
        } else if self.checking_large_theorem.get() {
            // Huge theorem: stay below circuit Regulars (~3k–7k). Large
            // *defs* (matchers) still use CIRCUIT so helpers unfold.
            CEILING
        } else {
            CIRCUIT
        };
        self.def_body_under(n, cap)
    }

    fn def_body_under(&self, n: u32, cap: u32) -> bool {
        match self.env.get(n) {
            Some(ConstantInfo::Def {
                hints: ReducibilityHints::Abbrev,
                ..
            }) => true,
            Some(ConstantInfo::Def { value, .. }) => expr_size_capped(value, cap) < cap,
            Some(ConstantInfo::Theorem { value, .. }) => expr_size_capped(value, cap) < cap,
            _ => false,
        }
    }

    fn is_delta_reducible(&self, n: u32) -> bool {
        // Lean's kernel unfolds any constant with a value, theorems included
        // (see `is_delta`/`unfold_definition` in the C++ kernel, which check
        // only `has_value`). Theorems must be paired with `unfold_def` actually
        // returning their value; making them reducible alone made `delta_step`
        // a no-op and `is_def_eq_core` loop. Opaque/quot/inductive/recursor
        // constants have no kernel value and stay irreducible.
        //
        // `KIOTA_NO_THEOREM_DELTA` must keep this consistent with
        // `unfold_delta`; an unfold guard that claims reducibility while
        // `delta_step` returns the term unchanged loops forever.
        let is_thm_kind = matches!(self.env.get(n), Some(ConstantInfo::Theorem { .. }));
        // Unset scope is global, but only small theorem bodies unfold
        // (opaque-unless-small). Large proofs stay folded so Check of
        // equation lemmas does not intern-explode or mis-reduce.
        let is_thm = is_thm_kind
            && std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_none()
            && crate::stats::theorem_delta_in_scope()
            && self.delta_body_is_small(n);
        matches!(self.env.get(n), Some(ConstantInfo::Def { .. })) || is_thm
    }

    // ---------------- Definitional equality ----------------

    pub fn is_def_eq(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let depth = DEFEQ_DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        if depth > 2048 {
            DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            if depth == 2049 && std::env::var_os("KIOTA_DEBUG").is_some() {
                eprintln!(
                    "DEFEQ_DEPTH a={} b={}",
                    self.pp_budget(a, 50),
                    self.pp_budget(b, 50)
                );
            }
            return Ok(false);
        }
        let r = self.is_def_eq_inner(ctx, a, b);
        DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        r
    }

    fn is_def_eq_inner(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        crate::stats::defeq_call();
        if crate::stats::enabled() {
            let n = crate::stats::defeq_calls();
            if n > 0 && n % 20_000 == 0 {
                eprintln!(
                    "MEM defeq={n} whnf={} core={} defeqc={} unfold={} infer={}",
                    self.whnf_cache.borrow().len(),
                    self.whnf_core_cache.borrow().len(),
                    self.defeq_cache.borrow().len(),
                    self.unfold_cache.borrow().len(),
                    self.infer_cache.borrow().len(),
                );
            }
        }
        if Rc::ptr_eq(a, b) || a == b {
            return Ok(true);
        }
        let (ka, kb) = (Self::ptr_key(a), Self::ptr_key(b));
        let (min_k, max_k) = if ka <= kb { (ka, kb) } else { (kb, ka) };
        // BVar defeq depends on the local telescope (`HetT.ext`: x.small vs
        // y.small are distinct bvars that become PI-equal only after
        // `Property` is unified). A ctx-free cache poisoned those pairs.
        let key = (ctx.id, min_k, max_k);
        if let Some(&r) = self.defeq_cache.borrow().get(&key) {
            return Ok(r);
        }
        if self.try_unreduced_const_congruence(ctx, a, b)? {
            self.defeq_cache.borrow_mut().insert(key, true);
            return Ok(true);
        }
        let aw = self.whnf_for_defeq(ctx, a)?;
        let bw = self.whnf_for_defeq(ctx, b)?;
        if std::env::var_os("KIOTA_TRACE_LINEAR").is_some() {
            let pa = self.pp_budget(a, 24);
            let pb = self.pp_budget(b, 24);
            if pa.contains("norm_eq_cert") || pb.contains("norm_eq_cert") {
                eprintln!(
                    "DEFEQ_WHNF a={} b={} aw={} bw={}",
                    pa,
                    pb,
                    self.pp_budget(&aw, 24),
                    self.pp_budget(&bw, 24)
                );
            }
        }
        if let (Ok(Some(x)), Ok(Some(y))) = (
            self.closed_int_value(ctx, &aw),
            self.closed_int_value(ctx, &bw),
        ) {
            let r = x == y;
            self.defeq_cache.borrow_mut().insert(key, r);
            return Ok(r);
        }
        let r = self.is_def_eq_core(ctx, &aw, &bw)?;
        self.defeq_cache.borrow_mut().insert(key, r);
        Ok(r)
    }

    fn is_def_eq_core(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let r = self.is_def_eq_core_go(ctx, a, b)?;
        if !r && crate::stats::trace_neq() {
            eprintln!(
                "NEQ[{}]  {}   ###   {}",
                ctx.len(),
                self.pp_budget(a, 60),
                self.pp_budget(b, 60)
            );
        }
        if !r && std::env::var_os("KIOTA_TRACE_NEG").is_some() {
            let pa = self.pp_budget(a, 40);
            let pb = self.pp_budget(b, 40);
            if pa.contains("4294967296") || pb.contains("4294967296") {
                eprintln!("NEQ32[{}]  {pa}   ###   {pb}", ctx.len());
            }
        }
        Ok(r)
    }

    fn is_def_eq_core_go(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        if crate::stats::verbose() {
            let binders = ctx
                .tys
                .iter()
                .map(|t| self.pp_budget(t, 14))
                .collect::<Vec<_>>()
                .join(" | ");
            eprintln!(
                "DEFEQ[{}:{}]  {}   ###   {}",
                ctx.len(),
                binders,
                self.pp_budget(a, 60),
                self.pp_budget(b, 60),
            );
        }
        if Rc::ptr_eq(a, b) || a == b {
            return Ok(true);
        }
        // Proof irrelevance for distinct bvars (`HetT.ext`: `x.small` vs
        // `y.small` after `cases h : Property_x = Property_y`). Lean treats
        // any two inhabitants of the same Prop as defeq; we used to wait
        // until after congruence, which left `USquash α s₁`  confusable
        // with `USquash α s₂`.
        if self.proofs_of_same_prop(ctx, a, b)? {
            return Ok(true);
        }
        if let Some((zero, succ)) = self.nat_ctors() {
            if let (Some(x), Some(y)) = (
                nat::numeral_value(a, zero, succ),
                nat::numeral_value(b, zero, succ),
            ) {
                return Ok(x == y);
            }
        }
        {
            let (h1, _) = expr::unfold_apps(a);
            if let ExprData::Const(n, _) = &**h1 {
                if matches!(self.env.get(*n), Some(ConstantInfo::Theorem { .. })) {
                    let same = self.with_infer_only(|| -> R<bool> {
                        let ta = match self.infer_type(ctx, a) {
                            Ok(t) => t,
                            Err(_) => return Ok(false),
                        };
                        if !self.is_prop(ctx, &ta)? {
                            return Ok(false);
                        }
                        let tb = match self.infer_type(ctx, b) {
                            Ok(t) => t,
                            Err(_) => return Ok(false),
                        };
                        self.is_def_eq(ctx, &ta, &tb)
                    })?;
                    if same {
                        return Ok(true);
                    }
                }
            }
        }
        // Structural match without delta.
        match (&***a, &***b) {
            (ExprData::Sort(l1), ExprData::Sort(l2)) => return Ok(level::is_def_eq(l1, l2)),
            (ExprData::BVar(i), ExprData::BVar(j)) if i == j => return Ok(true),
            (ExprData::Lit(x), ExprData::Lit(y)) => return Ok(x == y),
            (ExprData::Pi(_, t1, b1), ExprData::Pi(_, t2, b2)) => {
                if !self.is_def_eq(ctx, t1, t2)? {
                    return Ok(false);
                }
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(t1.clone());
                return self.is_def_eq(&ctx2, b1, b2);
            }
            (ExprData::Lam(_, t1, b1), ExprData::Lam(_, t2, b2)) => {
                let _ = self.is_def_eq(ctx, t1, t2)?; // domains needn't match strictly if only used for eta-shape; keep permissive
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(t1.clone());
                return self.is_def_eq(&ctx2, b1, b2);
            }
            (ExprData::App(_, _), ExprData::App(_, _)) => {
                let (h1, a1) = expr::unfold_apps(a);
                let (h2, a2) = expr::unfold_apps(b);
                if let (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) = (&**h1, &**h2) {
                    if n1 == n2
                        && a1.len() == a2.len()
                        && u1.len() == u2.len()
                        && u1
                            .iter()
                            .zip(u2.iter())
                            .all(|(x, y)| level::is_def_eq(x, y))
                    {
                        let ok = if self.const_has_proof_arg(*n1) {
                            match self.infer_const(*n1, u1) {
                                Ok(fn_ty) => self.defeq_args(ctx, &fn_ty, &a1, &a2)?,
                                Err(_) => self.pairwise_args(ctx, &a1, &a2)?,
                            }
                        } else {
                            self.pairwise_args(ctx, &a1, &a2)?
                        };
                        if ok {
                            return Ok(true);
                        }
                    }
                } else if a1.len() == a2.len() {
                    // Congruence under any shared head, not just a bound
                    // variable or a Const. Restricting this to BVar left
                    // `f x` and `f y` uncomparable whenever `f` was, say, a
                    // projection: the Const arm does not apply, and the delta
                    // path below cannot fire because neither head is a Const.
                    // Init hits this at Std.Iterator.step, where the shared
                    // head is `Std.Internal.idOpaque ….0[Subtype]`.
                    //
                    // Pointer-equal heads are the common case; when they
                    // differ but are *definitionally* equal we must still
                    // compare, otherwise a pair like
                    //   `(Nat.rec … #1).0[PProd] #2` vs
                    //   `(Nat.rec … (#1+0)).0[PProd] #2`
                    // dies at the delta path's `(None, None)` dead end
                    // (neither spine head is a Const). Two Const heads are
                    // left to the delta path, which handles unfolding.
                    let head_eq = Rc::ptr_eq(&h1, &h2)
                        || (!matches!(&**h1, ExprData::Const(..))
                            && !matches!(&**h2, ExprData::Const(..))
                            && self.is_def_eq(ctx, &h1, &h2)?);
                    if head_eq {
                        let ok = if let ExprData::Const(n, us) = &**h1 {
                            if self.const_has_proof_arg(*n) {
                                match self.infer_const(*n, us) {
                                    Ok(fn_ty) => self.defeq_args(ctx, &fn_ty, &a1, &a2)?,
                                    Err(_) => self.pairwise_args(ctx, &a1, &a2)?,
                                }
                            } else {
                                self.pairwise_args(ctx, &a1, &a2)?
                            }
                        } else {
                            self.pairwise_args(ctx, &a1, &a2)?
                        };
                        if ok {
                            return Ok(true);
                        }
                    }
                }
            }
            (ExprData::Proj(s1, i1, v1), ExprData::Proj(s2, i2, v2)) => {
                // Congruence for projections. Without this, two projections of
                // structures that are equal but not syntactically identical
                // never get compared field-wise: neither side has a Const head,
                // so the delta path below cannot fire either, and the terms are
                // reported unequal. Init.Prelude reaches exactly that case in
                // Classical.em, where `Classical.choose` unfolds to a `.val`
                // projection of `indefiniteDescription`.
                //
                // Falls through rather than returning false, so structure eta
                // and the reductions below still get their turn.
                if s1 == s2 && i1 == i2 && self.is_def_eq(ctx, v1, v2)? {
                    return Ok(true);
                }
            }
            (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) => {
                if n1 == n2
                    && u1.len() == u2.len()
                    && u1
                        .iter()
                        .zip(u2.iter())
                        .all(|(x, y)| level::is_def_eq(x, y))
                {
                    return Ok(true);
                }
            }
            _ => {}
        }

        // Eta for lambdas: one side a lambda, other not -> eta-expand other.
        if let (ExprData::Lam(_, t1, _), _) = (&***a, &***b) {
            if !matches!(&***b, ExprData::Lam(_, _, _)) {
                let b_app = expr::app(expr::shift(b, 1, 0), expr::bvar(0));
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(t1.clone());
                let a_body = if let ExprData::Lam(_, _, bd) = &***a {
                    bd.clone()
                } else {
                    unreachable!()
                };
                return self.is_def_eq(&ctx2, &a_body, &b_app);
            }
        }
        if let (_, ExprData::Lam(_, t2, _)) = (&***a, &***b) {
            if !matches!(&***a, ExprData::Lam(_, _, _)) {
                let a_app = expr::app(expr::shift(a, 1, 0), expr::bvar(0));
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(t2.clone());
                let b_body = if let ExprData::Lam(_, _, bd) = &***b {
                    bd.clone()
                } else {
                    unreachable!()
                };
                return self.is_def_eq(&ctx2, &a_app, &b_body);
            }
        }

        // Unit-like: any two elements of a 0-field, 0-index, 1-ctor, non-recursive
        // structure are definitionally equal (Unit, PUnit.{u}, NewSingleton, …).
        if self.is_unit_like_pair(ctx, a, b)? {
            return Ok(true);
        }

        // Structure eta: a is a constructor application (single-ctor struct) vs
        // an arbitrary term b of the same (inductive) type, or vice versa.
        if let Some(r) = self.try_struct_eta(ctx, a, b)? {
            if r {
                return Ok(true);
            }
        }
        if let Some(r) = self.try_struct_eta(ctx, b, a)? {
            if r {
                return Ok(true);
            }
        }

        // Delta: unfold whichever side has higher (or any) delta height, retry.
        let (h1, _) = expr::unfold_apps(a);
        let (h2, _) = expr::unfold_apps(b);
        let n1 = if let ExprData::Const(n, _) = &**h1 {
            Some(*n)
        } else {
            None
        };
        let n2 = if let ExprData::Const(n, _) = &**h2 {
            Some(*n)
        } else {
            None
        };
        if std::env::var_os("KIOTA_TRACE_DELTA").is_some() {
            eprintln!(
                "DELTA n1={:?} n2={:?}  {}   ###   {}",
                n1.map(|n| self.name_str(n).to_string()),
                n2.map(|n| self.name_str(n).to_string()),
                self.pp_budget(a, 60),
                self.pp_budget(b, 60),
            );
        }
        let delta_res = match (n1, n2) {
            (Some(x), Some(y)) if x == y => {
                // Args already failed congruence. Unfolding the *same* body
                // only helps unused parameters; huge same-head Regulars
                // must not be instantiated.
                if self.is_delta_reducible(x) && self.delta_body_is_small(x) {
                    let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                    let ub = self.whnf_core(ctx, &self.delta_step(b)?)?;
                    self.is_def_eq_core(ctx, &ua, &ub)
                } else {
                    Ok(false)
                }
            }
            (Some(x), Some(y)) => {
                let hx = self.def_height(x);
                let hy = self.def_height(y);
                let rx = self.is_delta_reducible(x) && self.eager_whnf_unfolds(x);
                let ry = self.is_delta_reducible(y) && self.eager_whnf_unfolds(y);
                if rx && (hx >= hy || !ry) {
                    let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                    self.is_def_eq_core(ctx, &ua, b)
                } else if ry {
                    let ub = self.whnf_core(ctx, &self.delta_step(b)?)?;
                    self.is_def_eq_core(ctx, a, &ub)
                } else {
                    Ok(false)
                }
            }
            (Some(x), None) if self.is_delta_reducible(x) && self.eager_whnf_unfolds(x) => {
                let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                self.is_def_eq_core(ctx, &ua, b)
            }
            (None, Some(y)) if self.is_delta_reducible(y) && self.eager_whnf_unfolds(y) => {
                let ub = self.whnf_core(ctx, &self.delta_step(b)?)?;
                self.is_def_eq_core(ctx, a, &ub)
            }
            _ => Ok(false),
        }?;

        if delta_res {
            return Ok(true);
        }

        // Proof irrelevance: two *proofs* of the same proposition are equal.
        if !self.obviously_not_proof(a) && !self.obviously_not_proof(b) {
            let same = self.with_infer_only(|| -> R<bool> {
                let ta = match self.infer_type(ctx, a) {
                    Ok(t) => t,
                    Err(_) => return Ok(false),
                };
                if !self.is_prop(ctx, &ta)? {
                    return Ok(false);
                }
                let tb = match self.infer_type(ctx, b) {
                    Ok(t) => t,
                    Err(_) => return Ok(false),
                };
                self.is_def_eq(ctx, &ta, &tb)
            })?;
            if same {
                return Ok(true);
            }
        }

        Ok(false)
    }

    fn delta_step(&self, e: &Expr) -> R<Expr> {
        let (head, args) = expr::unfold_apps(e);
        if let ExprData::Const(n, us) = &**head {
            if let Some(u) = self.unfold_delta(
                *n,
                us,
                crate::stats::theorem_delta_in_scope() && self.delta_body_is_small(*n),
            )? {
                return Ok(expr::apps(u, &args));
            }
        }
        Ok(e.clone())
    }

    fn try_struct_eta(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<Option<bool>> {
        // a must whnf to `Ctor params.. fields..` for a single-ctor inductive,
        // and we compare each field of a against `proj(b, i)`, plus check
        // b's type matches.
        let (ha, argsa) = expr::unfold_apps(a);
        let (cname, num_params) = match &**ha {
            ExprData::Const(n, _) => match self.env.get(*n) {
                Some(ConstantInfo::Constructor {
                    induct, num_params, ..
                }) => (*induct, *num_params),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let is_struct = matches!(
            self.env.get(cname),
            Some(ConstantInfo::InductiveType { ctors, num_indices, is_rec, .. })
                if ctors.len() == 1 && *num_indices == 0 && !*is_rec
        );
        if !is_struct {
            return Ok(None);
        }
        let num_fields = argsa.len().saturating_sub(num_params as usize);
        if num_fields == 0 && argsa.len() < num_params as usize {
            return Ok(None);
        }
        let fields = &argsa[num_params as usize..];
        for (i, f) in fields.iter().enumerate() {
            let p = expr::proj(cname, i as u32, b.clone());
            if !self.is_def_eq(ctx, f, &p)? {
                return Ok(Some(false));
            }
        }
        Ok(Some(true))
    }

    /// Cap one consecutive `Nat.rec` countdown of a `bits() >= 20` literal.
    /// `Poly.cancelAux hugeFuel` (`1e6`) as a million-step countdown is the
    /// `#3256` hang. A global-per-decl budget of 2048 false-rejects grind
    /// `_proof_1_1` (`simp_cert` stuck vs `eagerReduce` true): that proof
    /// does ~26382 hugeFuel peels as many short O(|poly|) countdowns.
    const FUEL_NAT_LIT_PEEL_MAX: u32 = 2048;

    fn try_iota(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let (rname, us) = match &***head {
            ExprData::Const(n, us) => (*n, us.clone()),
            _ => return Ok(None),
        };
        if crate::stats::verbose() {
            eprintln!("try_iota on: {}", self.name_str(rname));
        }
        let (level_params, all, num_params, num_motives, num_minors, num_indices) =
            match self.env.get(rname) {
                Some(ConstantInfo::Recursor {
                    level_params,
                    all,
                    num_params,
                    num_motives,
                    num_minors,
                    num_indices,
                    ..
                }) => (
                    level_params.clone(),
                    all.clone(),
                    *num_params,
                    *num_motives,
                    *num_minors,
                    *num_indices,
                ),
                _ => return Ok(None),
            };
        let rec_owns_ctor = |cname: u32| -> bool {
            match self.env.get(rname) {
                Some(ConstantInfo::Recursor { rules, .. }) => rules.iter().any(|r| r.ctor == cname),
                _ => false,
            }
        };
        let major_pos = (num_params + num_motives + num_minors + num_indices) as usize;
        if args.len() <= major_pos {
            return Ok(None);
        }
        let params = &args[..num_params as usize];
        let motives = &args[num_params as usize..(num_params + num_motives) as usize];
        let minors = &args
            [(num_params + num_motives) as usize..(num_params + num_motives + num_minors) as usize];
        let major = &args[major_pos];
        let rest = &args[major_pos + 1..];

        let k_like = self.is_k_like(&all)?;

        let major_w = self.whnf_major(ctx, major, rname)?;
        let (mhead, margs) = expr::unfold_apps(&major_w);

        let ctor = match &**mhead {
            ExprData::Const(cname, _) => match self.env.get(*cname) {
                Some(ConstantInfo::Constructor {
                    induct,
                    num_params: cnp,
                    ..
                }) if all.contains(induct) || rec_owns_ctor(*cname) => {
                    Some((*cname, *cnp, margs.clone()))
                }
                _ => None,
            },
            ExprData::Lit(Lit::Nat(n)) => {
                if let Some((zero, succ)) = self.nat_ctors() {
                    let nat_induct = match self.env.get(zero) {
                        Some(ConstantInfo::Constructor { induct, .. }) => Some(*induct),
                        _ => None,
                    };
                    if nat_induct.map(|ind| all.contains(&ind)).unwrap_or(false)
                        || rec_owns_ctor(zero)
                    {
                        if n == &num_bigint::BigUint::from(0u32) {
                            Some((zero, 0, vec![]))
                        } else if n.bits() > 24 {
                            // `UInt32.toNat_shiftLeft` peels `2^32` (33 bits).
                            None
                        } else if n.bits() >= 20 {
                            // Count consecutive peels of one literal
                            // (`n`, `n-1`, …). Do not cap 16–19 bit peels:
                            // `assemble₂._proof_2` needs those.
                            let consecutive = match self.fuel_nat_last.borrow().as_ref() {
                                Some(prev) if *prev == n + 1u32 => self.fuel_nat_peels.get() + 1,
                                _ => 1,
                            };
                            if consecutive > Self::FUEL_NAT_LIT_PEEL_MAX {
                                None
                            } else {
                                self.fuel_nat_peels.set(consecutive);
                                *self.fuel_nat_last.borrow_mut() = Some(n.clone());
                                let pred = n - 1u32;
                                Some((succ, 0, vec![expr::lit_nat(pred)]))
                            }
                        } else {
                            let pred = n - 1u32;
                            Some((succ, 0, vec![expr::lit_nat(pred)]))
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };

        let (cname, cnp, ctor_args) = if let Some(x) = ctor {
            x
        } else if let Some(x) = self.to_ctor_when_structure(ctx, &all, params, major)? {
            x
        } else if k_like {
            match self.k_like_ctor(ctx, &all, params, major)? {
                Some(x) => x,
                None => return Ok(None),
            }
        } else {
            return Ok(None);
        };

        if (ctor_args.len() as u32) < cnp {
            return Ok(None);
        }
        let ctor_params = &ctor_args[..cnp as usize];
        let fields = &ctor_args[cnp as usize..];

        let minor_idx = self.ctor_minor_index(cname, rname, &all);
        if minor_idx >= minors.len() {
            return Ok(None);
        }
        let rhs = self.iota_from_first_principles(
            ctx,
            rname,
            &us,
            &level_params,
            &all,
            params,
            ctor_params,
            motives,
            minors,
            minors[minor_idx].clone(),
            cname,
            fields,
        )?;
        Ok(Some(expr::apps(rhs, rest)))
    }

    /// K-like iff: not mutual, result sort is Prop, one constructor, zero fields.
    /// Independently computed; the exported `k` flag is never trusted.
    fn is_k_like(&self, all: &[u32]) -> R<bool> {
        if all.len() != 1 {
            return Ok(false);
        }
        let tname = all[0];
        let (ctors, num_params, typ) = match self.env.get(tname) {
            Some(ConstantInfo::InductiveType {
                ctors,
                num_params,
                typ,
                ..
            }) => (ctors.clone(), *num_params, typ.clone()),
            _ => return Ok(false),
        };
        if ctors.len() != 1 {
            return Ok(false);
        }
        let mut ctx: Ctx = Ctx::new();
        let mut cur = typ;
        for _ in 0..num_params {
            match self.ensure_pi(&ctx, &cur) {
                Ok((_, dom, body)) => {
                    ctx.push(dom);
                    cur = body;
                }
                Err(_) => return Ok(false),
            }
        }
        loop {
            match self.whnf(&ctx, &cur) {
                Ok(w) => match &**w {
                    ExprData::Pi(_, dom, body) => {
                        ctx.push(dom.clone());
                        cur = body.clone();
                    }
                    _ => {
                        cur = w;
                        break;
                    }
                },
                Err(_) => return Ok(false),
            }
        }
        let lvl = match self.ensure_sort(&ctx, &cur) {
            Ok(l) => l,
            Err(_) => return Ok(false),
        };
        if !level::is_def_eq(&lvl, &level::zero()) {
            return Ok(false);
        }
        let ctor_typ = match self.env.get(ctors[0]) {
            Some(ConstantInfo::Constructor { typ, .. }) => typ.clone(),
            _ => return Ok(false),
        };
        let mut nfields = 0u32;
        let mut ct = ctor_typ;
        loop {
            match &**ct {
                ExprData::Pi(_, _, body) => {
                    nfields += 1;
                    ct = body.clone();
                }
                _ => break,
            }
        }
        Ok(nfields == num_params)
    }

    fn k_like_ctor(
        &self,
        ctx: &Ctx,
        all: &[u32],
        params: &[Expr],
        major: &Expr,
    ) -> R<Option<(u32, u32, Vec<Expr>)>> {
        let tname = all[0];
        let (ctors, _num_params) = match self.env.get(tname) {
            Some(ConstantInfo::InductiveType {
                ctors, num_params, ..
            }) if ctors.len() == 1 => (ctors.clone(), *num_params),
            _ => return Ok(None),
        };
        let cname = ctors[0];
        let (ctor_lp, ctor_typ, cnp) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                num_params: cnp,
                ..
            }) => (level_params.clone(), typ.clone(), *cnp),
            _ => return Ok(None),
        };
        let mt = self.infer_type(ctx, major)?;
        let mtw = self.whnf(ctx, &mt)?;
        let (thead, targs) = expr::unfold_apps(&mtw);
        match &**thead {
            ExprData::Const(n, us) if *n == tname => {
                let subst = level::subst_map(&ctor_lp, us);
                let mut ct = expr::instantiate_level_params(&ctor_typ, &subst);
                for p in params {
                    match self.ensure_pi(ctx, &ct) {
                        Ok((_, _, body)) => ct = expr::instantiate1(&body, p),
                        Err(_) => return Ok(None),
                    }
                }
                let (_, ctor_res_args) = expr::unfold_apps(&ct);
                if targs.len() != ctor_res_args.len() {
                    return Ok(None);
                }
                for (a, b) in targs.iter().zip(ctor_res_args.iter()) {
                    if !self.is_def_eq(ctx, a, b)? {
                        return Ok(None);
                    }
                }
                Ok(Some((cname, cnp, params.to_vec())))
            }
            _ => Ok(None),
        }
    }

    fn rec_group(&self, rname: u32) -> Vec<u32> {
        self.env
            .rec_group
            .get(&rname)
            .cloned()
            .unwrap_or_else(|| vec![rname])
    }

    fn rec_for_ctor_in_group(&self, cname: u32, rname: u32) -> Option<u32> {
        for rec in self.rec_group(rname) {
            if let Some(ConstantInfo::Recursor { rules, .. }) = self.env.get(rec) {
                if rules.iter().any(|r| r.ctor == cname) {
                    return Some(rec);
                }
            }
        }
        None
    }

    fn nested_rec_for(&self, type_name: u32, rname: u32) -> Option<u32> {
        let ctors = match self.env.get(type_name) {
            Some(ConstantInfo::InductiveType { ctors, .. }) => ctors,
            _ => return None,
        };
        for c in ctors {
            if let Some(rec) = self.rec_for_ctor_in_group(*c, rname) {
                return Some(rec);
            }
        }
        None
    }

    fn ctor_minor_index(&self, cname: u32, rname: u32, all: &[u32]) -> usize {
        let mut idx = 0usize;
        for rec in self.rec_group(rname) {
            if let Some(ConstantInfo::Recursor { rules, .. }) = self.env.get(rec) {
                for rule in rules {
                    if rule.ctor == cname {
                        return idx;
                    }
                    idx += 1;
                }
            }
        }
        // Fallback: main-type ctor order (non-nested groups).
        idx = 0;
        for t in all {
            let ctors = match self.env.get(*t) {
                Some(ConstantInfo::InductiveType { ctors, .. }) => ctors,
                _ => continue,
            };
            for c in ctors {
                if *c == cname {
                    return idx;
                }
                idx += 1;
            }
        }
        idx
    }

    fn iota_from_first_principles(
        &self,
        ctx: &Ctx,
        rname: u32,
        us: &[Level],
        level_params: &[u32],
        all: &[u32],
        params: &[Expr],
        ctor_params: &[Expr],
        motives: &[Expr],
        minors: &[Expr],
        minor: Expr,
        cname: u32,
        fields: &[Expr],
    ) -> R<Expr> {
        let (ctor_lp, ctor_typ) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                level_params, typ, ..
            }) => (level_params.clone(), typ.clone()),
            _ => return Ok(minor),
        };
        let subst = level::subst_map(&ctor_lp, us);
        let mut ct = expr::instantiate_level_params(&ctor_typ, &subst);
        // Nested ctors (Array.mk, List.cons) carry their own params on the
        // major; the outer recursor's params may be empty (Syntax).
        for p in ctor_params {
            let (_, _, body) = self.ensure_pi(ctx, &ct)?;
            ct = expr::instantiate1(&body, p);
        }
        // Lean iota: apply every constructor field first, then one rec-call
        // per recursive field, in field order. Interleaving (field, rec, field)
        // is wrong as soon as two fields are recursive (RBTree.red, etc.).
        let mut result = minor;
        let mut rec_calls: Vec<Expr> = Vec::new();
        let mut cctx = ctx.clone();
        for f in fields {
            let (_, dom, body) = match self.ensure_pi(&cctx, &ct) {
                Ok(x) => x,
                Err(_) => break,
            };
            result = expr::app(result, f.clone());
            if let Some(rec_call) =
                self.mk_rec_call(&cctx, rname, us, all, params, motives, minors, f, &dom)?
            {
                rec_calls.push(rec_call);
            }
            // `instantiate1` discharges the binder that `ensure_pi` peeled,
            // so the next `ct` lives at the same depth as this one. Pushing
            // `dom` here grew the context anyway, leaving every later field
            // checked one binder too deep — the whole spine came out with
            // indices uniformly off by one, which is how Init's
            // Array.foldlM_toList.aux._unary failed.
            ct = expr::instantiate1(&body, f);
        }
        for rec_call in rec_calls {
            result = expr::app(result, rec_call);
        }
        let _ = (level_params,);
        Ok(result)
    }

    fn mk_rec_call(
        &self,
        ctx: &Ctx,
        rname: u32,
        us: &[Level],
        all: &[u32],
        params: &[Expr],
        motives: &[Expr],
        minors: &[Expr],
        field: &Expr,
        field_ty: &Expr,
    ) -> R<Option<Expr>> {
        let is_rec = match self.env.get(rname) {
            Some(ConstantInfo::Recursor { all, .. }) => {
                all.iter().any(|t| match self.env.get(*t) {
                    Some(ConstantInfo::InductiveType { is_rec, .. }) => *is_rec,
                    _ => false,
                })
            }
            _ => true,
        };
        if !is_rec {
            return Ok(None);
        }
        let mut ty = self
            .whnf(ctx, field_ty)
            .unwrap_or_else(|_| field_ty.clone());
        let mut binders: Vec<Expr> = Vec::new();
        let mut tctx = ctx.clone();
        loop {
            match &**ty {
                ExprData::Pi(_, dom, body) => {
                    binders.push(dom.clone());
                    tctx.push(dom.clone());
                    ty = self.whnf(&tctx, body).unwrap_or_else(|_| body.clone());
                }
                _ => break,
            }
        }
        let (head, iargs) = expr::unfold_apps(&ty);
        let target = match &**head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let shift_by = binders.len() as i32;
        let (rec_name, rec_params, indices): (u32, Vec<Expr>, &[Expr]) = if all.contains(&target) {
            let rec = self.env.rec_of.get(&target).copied().unwrap_or(rname);
            let nparams = match self.env.get(rec) {
                Some(ConstantInfo::Recursor { num_params, .. }) => *num_params as usize,
                _ => params.len(),
            };
            if iargs.len() < nparams || nparams != params.len() {
                return Ok(None);
            }
            for (p_field, p_rec) in iargs[..nparams].iter().zip(params.iter()) {
                let p_rec_shifted = expr::shift(p_rec, shift_by, 0);
                if !self.is_def_eq(&tctx, p_field, &p_rec_shifted)? {
                    return Ok(None);
                }
            }
            (rec, iargs[..nparams].to_vec(), &iargs[nparams..])
        } else if self.occurs_any(&ty, all) {
            // Only `F … I …` (e.g. `Array Syntax`), not `List Preresolved`.
            if let Some(nrec) = self.nested_rec_for(target, rname) {
                (
                    nrec,
                    params.iter().map(|p| expr::shift(p, shift_by, 0)).collect(),
                    &[][..],
                )
            } else {
                return Ok(None);
            }
        } else {
            return Ok(None);
        };
        let rec = expr::const_(rec_name, us.to_vec());
        let mut rec_app = rec;
        for p in rec_params {
            rec_app = expr::app(rec_app, p);
        }
        for m in motives {
            rec_app = expr::app(rec_app, expr::shift(m, shift_by, 0));
        }
        for m in minors {
            rec_app = expr::app(rec_app, expr::shift(m, shift_by, 0));
        }
        for ix in indices {
            rec_app = expr::app(rec_app, ix.clone());
        }
        let mut fapp = expr::shift(field, binders.len() as i32, 0);
        for i in (0..binders.len()).rev() {
            fapp = expr::app(fapp, expr::bvar(i as u32));
        }
        rec_app = expr::app(rec_app, fapp);
        for (i, bty) in binders.iter().enumerate().rev() {
            let shifted = expr::shift(bty, i as i32, 0);
            rec_app = expr::lam(crate::expr::BinderInfo::Default, shifted, rec_app);
        }
        Ok(Some(rec_app))
    }

    fn try_quot(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let is_lift = matches!(
            self.env.get(n),
            Some(ConstantInfo::Quot {
                kind: QuotKind::Lift,
                ..
            })
        );
        let is_ind = matches!(
            self.env.get(n),
            Some(ConstantInfo::Quot {
                kind: QuotKind::Ind,
                ..
            })
        );
        if !is_lift && !is_ind {
            return Ok(None);
        }
        // Quot.lift : {α β} {r} (f : α → β) (h) (q : Quot r) → β
        //   Quot.lift f h (Quot.mk r a) ==> f a
        // Quot.ind  : {α} {r} {β : Quot r → Prop} (h : ∀ a, β (Quot.mk r a)) (q) → β q
        //   Quot.ind h (Quot.mk r a) ==> h a
        let (f_idx, q_idx, is_lift2) = if is_lift {
            (3usize, 5usize, true)
        } else {
            (3usize, 4usize, false)
        };
        if args.len() <= q_idx {
            return Ok(None);
        }
        let q = self.whnf(ctx, &args[q_idx])?;
        let (qhead, qargs) = expr::unfold_apps(&q);
        let is_mk = matches!(&**qhead, ExprData::Const(cn,_) if matches!(self.env.get(*cn), Some(ConstantInfo::Quot{kind: QuotKind::Ctor,..})));
        if !is_mk || qargs.len() < 3 {
            return Ok(None);
        }
        let a = &qargs[2];
        let f = &args[f_idx];
        let result = if is_lift2 {
            expr::app(f.clone(), a.clone())
        } else {
            expr::app(f.clone(), a.clone())
        };
        let rest = &args[q_idx + 1..];
        Ok(Some(expr::apps(result, rest)))
    }

    /// Whnf a Nat argument without expanding an existing nat lit to `succ`.
    fn reduce_nat_arg(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        if nat::as_lit(e).is_some() {
            return Ok(e.clone());
        }
        self.whnf(ctx, e)
    }

    /// Native Nat reductions (minimal): succ/add/beq/OfNat.
    fn try_nat_extension(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        match name {
            "Nat.succ" if !args.is_empty() => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                if let Some(v) = nat::as_lit(&a) {
                    let r = nat::mk_lit(nat::succ_value(v));
                    return Ok(Some(expr::apps(r, &args[1..])));
                }
                if let Some((zero, succ)) = self.nat_ctors() {
                    if let Some(v) = nat::numeral_value(&a, zero, succ) {
                        let r = nat::mk_lit(nat::succ_value(&v));
                        return Ok(Some(expr::apps(r, &args[1..])));
                    }
                }
                Ok(None)
            }
            "Nat.add" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                if let (Some(x), Some(y)) = (nat::as_lit(&a), nat::as_lit(&b)) {
                    let r = nat::mk_lit(nat::add_values(x, y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                if let Some((zero, succ)) = self.nat_ctors() {
                    if let (Some(x), Some(y)) = (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    ) {
                        let r = nat::mk_lit(nat::add_values(&x, &y));
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                    if nat::is_zero(&b, zero) {
                        return Ok(Some(expr::apps(a, &args[2..])));
                    }
                    if nat::is_zero(&a, zero) {
                        return Ok(Some(expr::apps(b, &args[2..])));
                    }
                    if nat::is_one(&b, zero, succ) {
                        let r = nat::mk_succ(succ, a);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                    // Do not succ-peel a large `Lit::Nat`: `Nat.add x 2147483395`
                    // would recurse ~2e9 times and overflow the stack
                    // (`Int32.instRxcHasSize_eq`).
                    let large_lit = |e: &Expr| nat::as_lit(e).is_some_and(|n| n.bits() >= 16);
                    if large_lit(&a) || large_lit(&b) {
                        return Ok(None);
                    }
                    if let Some(p) = nat::pred(&b, zero, succ) {
                        let add = expr::apps(expr::const_(n, vec![]), &[a, p]);
                        let r = nat::mk_succ(succ, add);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                    if let Some(p) = nat::pred(&a, zero, succ) {
                        let add = expr::apps(expr::const_(n, vec![]), &[p, b]);
                        let r = nat::mk_succ(succ, add);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.mul" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                if let (Some(x), Some(y)) = (nat::as_lit(&a), nat::as_lit(&b)) {
                    let r = nat::mk_lit(nat::mul_values(x, y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                let Some((zero, succ)) = self.nat_ctors() else {
                    return Ok(None);
                };
                if let (Some(x), Some(y)) = (
                    nat::numeral_value(&a, zero, succ),
                    nat::numeral_value(&b, zero, succ),
                ) {
                    let r = nat::mk_lit(nat::mul_values(&x, &y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                if nat::is_zero(&a, zero) || nat::is_zero(&b, zero) {
                    return Ok(Some(expr::apps(nat::mk_lit(0u32.into()), &args[2..])));
                }
                if nat::as_lit(&a).is_some_and(|n| n.bits() >= 16)
                    || nat::as_lit(&b).is_some_and(|n| n.bits() >= 16)
                {
                    return Ok(None);
                }
                if let Some(p) = nat::pred(&b, zero, succ) {
                    let mul = expr::apps(expr::const_(n, vec![]), &[a.clone(), p]);
                    if let Some(add) = self.find_name("Nat.add") {
                        let r = expr::apps(expr::const_(add, vec![]), &[mul, a]);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                if let Some(p) = nat::pred(&a, zero, succ) {
                    let mul = expr::apps(expr::const_(n, vec![]), &[p, b.clone()]);
                    if let Some(add) = self.find_name("Nat.add") {
                        let r = expr::apps(expr::const_(add, vec![]), &[mul, b]);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.sub" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                if let (Some(x), Some(y)) = (nat::as_lit(&a), nat::as_lit(&b)) {
                    let r = nat::mk_lit(nat::sub_values(x, y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                if let Some((zero, succ)) = self.nat_ctors() {
                    if nat::is_zero(&b, zero) {
                        return Ok(Some(expr::apps(a, &args[2..])));
                    }
                    if nat::is_zero(&a, zero) {
                        return Ok(Some(expr::apps(nat::mk_lit(0u32.into()), &args[2..])));
                    }
                    if let (Some(pa), Some(pb)) =
                        (nat::pred(&a, zero, succ), nat::pred(&b, zero, succ))
                    {
                        let r = expr::apps(expr::const_(n, vec![]), &[pa, pb]);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.pow" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    if let Some(v) = nat::pow_values(&x, &y) {
                        return Ok(Some(expr::apps(nat::mk_lit(v), &args[2..])));
                    }
                }
                let Some((zero, succ)) = self.nat_ctors() else {
                    return Ok(None);
                };
                if nat::is_zero(&b, zero) {
                    return Ok(Some(expr::apps(nat::mk_lit(1u32.into()), &args[2..])));
                }
                if let Some(p) = nat::pred(&b, zero, succ) {
                    let pow = expr::apps(expr::const_(n, vec![]), &[a.clone(), p]);
                    if let Some(mul) = self.find_name("Nat.mul") {
                        let r = expr::apps(expr::const_(mul, vec![]), &[pow, a]);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.div" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                if let (Some(x), Some(y)) = (nat::as_lit(&a), nat::as_lit(&b)) {
                    let r = nat::mk_lit(nat::div_values(x, y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                if let Some((zero, succ)) = self.nat_ctors() {
                    if let (Some(x), Some(y)) = (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    ) {
                        let r = nat::mk_lit(nat::div_values(&x, &y));
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.mod" | "Nat.modCore" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                if let (Some(x), Some(y)) = (nat::as_lit(&a), nat::as_lit(&b)) {
                    let r = nat::mk_lit(nat::mod_values(x, y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                if let Some((zero, succ)) = self.nat_ctors() {
                    if let (Some(x), Some(y)) = (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    ) {
                        let r = nat::mk_lit(nat::mod_values(&x, &y));
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.shiftLeft" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    if let Some(v) = nat::shift_left_values(&x, &y) {
                        return Ok(Some(expr::apps(nat::mk_lit(v), &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.shiftRight" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let r = nat::mk_lit(nat::shift_right_values(&x, &y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                Ok(None)
            }
            "Nat.land" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let r = nat::mk_lit(nat::land_values(&x, &y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                Ok(None)
            }
            "Nat.lor" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let r = nat::mk_lit(nat::lor_values(&x, &y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                Ok(None)
            }
            "Nat.xor" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let r = nat::mk_lit(nat::xor_values(&x, &y));
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
                Ok(None)
            }
            "HAdd.hAdd"
            | "Add.add"
            | "HMul.hMul"
            | "Mul.mul"
            | "HPow.hPow"
            | "Pow.pow"
            | "HSub.hSub"
            | "Sub.sub"
            | "HMod.hMod"
            | "Mod.mod"
            | "HDiv.hDiv"
            | "Div.div"
            | "HShiftLeft.hShiftLeft"
            | "ShiftLeft.shiftLeft"
            | "HShiftRight.hShiftRight"
            | "ShiftRight.shiftRight"
                if args.len() >= 2 =>
            {
                if let Some(r) = self.try_hbin_nat(ctx, name, args)? {
                    return Ok(Some(r));
                }
                Ok(None)
            }
            "Nat.ble" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let tname = if nat::ble_values(&x, &y) {
                        "Bool.true"
                    } else {
                        "Bool.false"
                    };
                    if let Some(bn) = self.find_name(tname) {
                        return Ok(Some(expr::apps(expr::const_(bn, vec![]), &args[2..])));
                    }
                }
                Ok(None)
            }
            "Nat.beq" if args.len() >= 2 => {
                let a = self.reduce_nat_arg(ctx, &args[0])?;
                let b = self.reduce_nat_arg(ctx, &args[1])?;
                let (va, vb) = if let Some((zero, succ)) = self.nat_ctors() {
                    (
                        nat::numeral_value(&a, zero, succ),
                        nat::numeral_value(&b, zero, succ),
                    )
                } else {
                    (nat::as_lit(&a).cloned(), nat::as_lit(&b).cloned())
                };
                if let (Some(x), Some(y)) = (va, vb) {
                    let tname = if nat::beq_values(&x, &y) {
                        "Bool.true"
                    } else {
                        "Bool.false"
                    };
                    if let Some(bn) = self.find_name(tname) {
                        return Ok(Some(expr::apps(expr::const_(bn, vec![]), &args[2..])));
                    }
                }
                Ok(None)
            }
            "Int.add" | "Int.sub" | "Int.mul" if args.len() >= 2 => {
                if let (Some(a), Some(b)) = (
                    self.closed_int_value(ctx, &args[0])?,
                    self.closed_int_value(ctx, &args[1])?,
                ) {
                    let v = match name {
                        "Int.add" => a + b,
                        "Int.sub" => a - b,
                        _ => a * b,
                    };
                    if let Some(r) = self.mk_closed_int(&v) {
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Int.pow" if args.len() >= 2 => {
                if let (Some(a), Some(e)) = (
                    self.closed_int_value(ctx, &args[0])?,
                    self.closed_nat_value(ctx, &args[1])?,
                ) {
                    if let Some(v) = int_pow(&a, &e) {
                        if let Some(r) = self.mk_closed_int(&v) {
                            return Ok(Some(expr::apps(r, &args[2..])));
                        }
                    }
                }
                Ok(None)
            }
            "Int.bmod" if args.len() >= 2 => {
                if let (Some(x), Some(m)) = (
                    self.closed_int_value(ctx, &args[0])?,
                    self.closed_nat_value(ctx, &args[1])?,
                ) {
                    if let Some(r) = self.mk_int_canonical(&int_bmod(&x, &m)) {
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Int.emod" if args.len() >= 2 => {
                if let Some(a) = self.closed_int_value(ctx, &args[0])? {
                    if let Some(m) = self.closed_nat_value(ctx, &args[1])? {
                        if let Some(r) = self.mk_int_canonical(&int_emod_nat(&a, &m)) {
                            return Ok(Some(expr::apps(r, &args[2..])));
                        }
                    } else if let Some(b) = self.closed_int_value(ctx, &args[1])? {
                        if b.sign() != Sign::Minus {
                            let m = b.magnitude().clone();
                            if let Some(r) = self.mk_int_canonical(&int_emod_nat(&a, &m)) {
                                return Ok(Some(expr::apps(r, &args[2..])));
                            }
                        }
                    }
                }
                Ok(None)
            }
            "Int.decLe" | "Int.decLt" if args.len() >= 2 => {
                let aw = self.whnf(ctx, &args[0])?;
                let bw = self.whnf(ctx, &args[1])?;
                let va = self.closed_int_value(ctx, &aw)?;
                let vb = self.closed_int_value(ctx, &bw)?;
                if let (Some(a), Some(b)) = (va, vb) {
                    let yes = if name == "Int.decLt" { a < b } else { a <= b };
                    if let Some(r) = self.mk_decidable_bool(yes) {
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Decidable.decide" | "decide" if args.len() >= 2 => {
                let inst = self.whnf(ctx, &args[1])?;
                let (ih, _) = expr::unfold_apps(&inst);
                let iname = match &**ih {
                    ExprData::Const(n, _) => self.name_str(*n),
                    _ => return Ok(None),
                };
                let tname = if matches!(iname, "Decidable.isTrue" | "isTrue") {
                    "Bool.true"
                } else if matches!(iname, "Decidable.isFalse" | "isFalse") {
                    "Bool.false"
                } else {
                    return Ok(None);
                };
                if let Some(bn) = self.find_name(tname) {
                    return Ok(Some(expr::apps(expr::const_(bn, vec![]), &args[2..])));
                }
                Ok(None)
            }
            "Int.neg" if !args.is_empty() => {
                // Canonical constructors, not `Int.neg (OfNat n)`: WHNF of
                // that form unfolds `Int.neg` into a `Nat.rec` of size `n`
                // (`Int32.toInt minValue` is `-(2^31)` and hits the hugeFuel
                // peel cap). `negSucc (n-1)` is already WHNF.
                if let Some(v) = self.closed_int_value(ctx, &args[0])? {
                    if let Some(r) = self.mk_int_canonical(&-v) {
                        return Ok(Some(expr::apps(r, &args[1..])));
                    }
                }
                // Peel the *raw* argument. Full WHNF would unfold the inner
                // `Int.neg` to `Int.rec` and the double-neg cancel would miss.
                if let Some(inner) = self.peel_int_neg(&args[0]) {
                    let inner_w = self.whnf(ctx, &inner)?;
                    if self.is_closed_int_numeral(&inner_w) {
                        return Ok(Some(expr::apps(inner_w, &args[1..])));
                    }
                }
                Ok(None)
            }
            "Int.ediv" | "Int.div" if args.len() >= 2 => {
                if let (Some(a), Some(b)) = (
                    self.closed_int_value(ctx, &args[0])?,
                    self.closed_int_value(ctx, &args[1])?,
                ) {
                    if let Some(r) = self.mk_closed_int(&int_ediv(&a, &b)) {
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "HDiv.hDiv" if args.len() >= 6 => {
                let ty = self.whnf(ctx, &args[0])?;
                let ty_name = match &**ty {
                    ExprData::Const(t, _) => self.name_str(*t),
                    _ => return Ok(None),
                };
                if ty_name == "Int" || ty_name.ends_with(".Int") {
                    if let (Some(a), Some(b)) = (
                        self.closed_int_value(ctx, &args[4])?,
                        self.closed_int_value(ctx, &args[5])?,
                    ) {
                        if let Some(r) = self.mk_closed_int(&int_ediv(&a, &b)) {
                            return Ok(Some(expr::apps(r, &args[6..])));
                        }
                    }
                }
                Ok(None)
            }
            "Int.natAbs" if !args.is_empty() => {
                if let Some(v) = self.closed_int_value(ctx, &args[0])? {
                    return Ok(Some(expr::apps(
                        expr::lit_nat(v.magnitude().clone()),
                        &args[1..],
                    )));
                }
                Ok(None)
            }
            "Nat.gcd" if args.len() >= 2 => {
                if let (Some(a), Some(b)) = (
                    self.closed_nat_value(ctx, &args[0])?,
                    self.closed_nat_value(ctx, &args[1])?,
                ) {
                    return Ok(Some(expr::apps(
                        expr::lit_nat(num_bigint_gcd(&a, &b)),
                        &args[2..],
                    )));
                }
                Ok(None)
            }
            "Neg.neg" if args.len() >= 3 => {
                let ty = self.whnf(ctx, &args[0])?;
                let ty_name = match &**ty {
                    ExprData::Const(t, _) => self.name_str(*t),
                    _ => return Ok(None),
                };
                if ty_name != "Int" && !ty_name.ends_with(".Int") {
                    return Ok(None);
                }
                if let Some(inner) = self.peel_int_neg(&args[2]) {
                    let inner_w = self.whnf(ctx, &inner)?;
                    let closed = self.is_closed_int_numeral(&inner_w);
                    if std::env::var_os("KIOTA_TRACE_NEG").is_some() {
                        eprintln!(
                            "NEG Neg.neg peel inner={} closed={closed}",
                            self.pp_budget(&inner_w, 24)
                        );
                    }
                    if closed {
                        return Ok(Some(expr::apps(inner_w, &args[3..])));
                    }
                }
                let Some(ineg) = self.find_name_ending("Int.neg") else {
                    return Ok(None);
                };
                let r = expr::app(expr::const_(ineg, vec![]), args[2].clone());
                return Ok(Some(expr::apps(r, &args[3..])));
            }
            "Nat.cast" | "NatCast.natCast" if args.len() >= 2 => {
                let (ty_i, val_i) = if name == "Nat.cast" && args.len() >= 3 {
                    (0usize, 2usize)
                } else if name == "NatCast.natCast" && args.len() >= 3 {
                    (0usize, 2usize)
                } else {
                    return Ok(None);
                };
                let ty = self.whnf(ctx, &args[ty_i])?;
                let ty_name = match &**ty {
                    ExprData::Const(t, _) => self.name_str(*t),
                    _ => return Ok(None),
                };
                if ty_name == "Int" || ty_name.ends_with(".Int") {
                    if let Some(n) = self.closed_nat_value(ctx, &args[val_i])? {
                        if let Some(r) = self.mk_closed_int(&BigInt::from(n)) {
                            return Ok(Some(expr::apps(r, &args[val_i + 1..])));
                        }
                    }
                }
                Ok(None)
            }
            "OfNat.ofNat" if args.len() >= 3 => {
                let Some(nat_ty) = self.nat_ref else {
                    return Ok(None);
                };
                let ty = self.whnf(ctx, &args[0])?;
                let mut stripped = args.to_vec();
                stripped[0] = ty.clone();
                if let Some(v) = nat::of_nat_value(&stripped, nat_ty) {
                    return Ok(Some(expr::apps(v, &args[3..])));
                }
                if let Some(v) = nat::of_nat_value(args, nat_ty) {
                    return Ok(Some(expr::apps(v, &args[3..])));
                }
                let ty_name = match &**ty {
                    ExprData::Const(t, _) => self.name_str(*t),
                    _ => return Ok(None),
                };
                if ty_name == "Int" || ty_name.ends_with(".Int") {
                    if let Some(n) = self.closed_nat_value(ctx, &args[1])? {
                        if let Some(ofn) = self.find_name_ending("Int.ofNat") {
                            let r = expr::app(expr::const_(ofn, vec![]), nat::mk_lit(n));
                            return Ok(Some(expr::apps(r, &args[3..])));
                        }
                    }
                }
                Ok(None)
            }
            n if (n == "Int.beq'" || n.ends_with(".Int.beq'")) && args.len() >= 2 => {
                if let (Some(a), Some(b)) = (
                    self.closed_int_value(ctx, &args[0])?,
                    self.closed_int_value(ctx, &args[1])?,
                ) {
                    let tname = if a == b { "Bool.true" } else { "Bool.false" };
                    if let Some(bn) = self.find_name(tname) {
                        return Ok(Some(expr::apps(expr::const_(bn, vec![]), &args[2..])));
                    }
                }
                Ok(None)
            }
            n if (n == "Bool.and'" || n.ends_with(".Bool.and'")) && args.len() >= 2 => {
                let a = self.whnf(ctx, &args[0])?;
                let b = self.whnf(ctx, &args[1])?;
                let ab = self.bool_const_val(&a);
                let bb = self.bool_const_val(&b);
                if let (Some(x), Some(y)) = (ab, bb) {
                    let tname = if x && y { "Bool.true" } else { "Bool.false" };
                    if let Some(bn) = self.find_name(tname) {
                        return Ok(Some(expr::apps(expr::const_(bn, vec![]), &args[2..])));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    fn bool_const_val(&self, e: &Expr) -> Option<bool> {
        let (h, _) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) => {
                let s = self.name_str(*n);
                if s == "Bool.true" || s.ends_with(".Bool.true") {
                    Some(true)
                } else if s == "Bool.false" || s.ends_with(".Bool.false") {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Class methods `HAdd.hAdd` / `Add.add` / `HMul.hMul` / `Mul.mul` on `Nat`.
    fn try_hbin_nat(&self, ctx: &Ctx, name: &str, args: &[Expr]) -> R<Option<Expr>> {
        let (ty_i, lhs_i, need) = match name {
            "HAdd.hAdd"
            | "HMul.hMul"
            | "HPow.hPow"
            | "HSub.hSub"
            | "HMod.hMod"
            | "HDiv.hDiv"
            | "HShiftLeft.hShiftLeft"
            | "HShiftRight.hShiftRight" => (0usize, 4usize, 6usize),
            "Add.add"
            | "Mul.mul"
            | "Pow.pow"
            | "Sub.sub"
            | "Mod.mod"
            | "Div.div"
            | "ShiftLeft.shiftLeft"
            | "ShiftRight.shiftRight" => (0usize, 2usize, 4usize),
            _ => return Ok(None),
        };
        if args.len() < need {
            return Ok(None);
        }
        let ty = self.whnf(ctx, &args[ty_i])?;
        let ty_name = match &**ty {
            ExprData::Const(t, _) => self.name_str(*t),
            _ => return Ok(None),
        };
        let is_nat = self
            .nat_ref
            .is_some_and(|n| matches!(&**ty, ExprData::Const(t, _) if *t == n));
        let is_combo = ty_name == "LinearCombo" || ty_name.ends_with(".LinearCombo");
        let is_int_name = |s: &str| s == "Int" || s.ends_with(".Int");
        // HMul Int IntList IntList has first type Int — do not rewrite to Int.mul.
        let is_int = if matches!(
            name,
            "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv" | "HMod.hMod"
        ) && args.len() >= 3
        {
            let t1 = self.whnf(ctx, &args[1])?;
            let t2 = self.whnf(ctx, &args[2])?;
            is_int_name(ty_name)
                && matches!(&**t1, ExprData::Const(t, _) if is_int_name(self.name_str(*t)))
                && matches!(&**t2, ExprData::Const(t, _) if is_int_name(self.name_str(*t)))
        } else {
            is_int_name(ty_name)
        };
        if !is_nat && !is_combo && !is_int {
            return Ok(None);
        }
        let op = if is_combo {
            match name {
                "HAdd.hAdd" | "Add.add" => "LinearCombo.add",
                "HSub.hSub" | "Sub.sub" => "LinearCombo.sub",
                _ => return Ok(None),
            }
        } else if is_int {
            match name {
                "HAdd.hAdd" | "Add.add" => "Int.add",
                "HSub.hSub" | "Sub.sub" => "Int.sub",
                "HMul.hMul" | "Mul.mul" => "Int.mul",
                "HPow.hPow" | "Pow.pow" => "Int.pow",
                _ => return Ok(None),
            }
        } else {
            match name {
                "HAdd.hAdd" | "Add.add" => "Nat.add",
                "HMul.hMul" | "Mul.mul" => "Nat.mul",
                "HPow.hPow" | "Pow.pow" => "Nat.pow",
                "HSub.hSub" | "Sub.sub" => "Nat.sub",
                "HMod.hMod" | "Mod.mod" => "Nat.mod",
                "HDiv.hDiv" | "Div.div" => "Nat.div",
                "HShiftLeft.hShiftLeft" | "ShiftLeft.shiftLeft" => "Nat.shiftLeft",
                "HShiftRight.hShiftRight" | "ShiftRight.shiftRight" => "Nat.shiftRight",
                _ => return Ok(None),
            }
        };
        let Some(opn) = self.find_name_ending(op) else {
            return Ok(None);
        };
        let lhs = args[lhs_i].clone();
        let rhs = args[lhs_i + 1].clone();
        let r = expr::apps(expr::const_(opn, vec![]), &[lhs, rhs]);
        Ok(Some(expr::apps(r, &args[need..])))
    }

    /// `dite α c (isTrue p h) t e → t h` and `isFalse` → `e h`.
    /// `ite` drops the proof. Fires in `whnf_core` so height-based delta
    /// cannot unfold a large Regular helper before the instance constructor
    /// is seen.
    /// Closed `Rat` projections / `inv`. `Rat.zpow_neg`'s `with_unfolding_all
    /// rfl` needs `1⁻¹ = 1`; `Rat.inv` is a `dite` on `a.num < 0` whose
    /// `Decidable` stays stuck unless `.num`/`.den` of `OfNat Rat n` reduce.
    fn try_rat(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let ident = name.rsplit('.').next().unwrap_or(name);
        let is_inv = ident == "inv" && (name.contains("Rat") || name.contains("Inv"));
        let is_num = ident == "num" && name.contains("Rat");
        let is_den = ident == "den" && name.contains("Rat");
        if !is_inv && !is_num && !is_den {
            return Ok(None);
        }
        if args.is_empty() {
            return Ok(None);
        }
        let a = args.last().unwrap();
        let Some((num, den, a_w)) = self.rat_closed_parts(ctx, a)? else {
            return Ok(None);
        };
        if is_num {
            let Some(e) = self.mk_closed_int(&num) else {
                return Ok(None);
            };
            return Ok(Some(expr::apps(e, &args[args.len()..])));
        }
        if is_den {
            return Ok(Some(expr::apps(expr::lit_nat(den), &args[args.len()..])));
        }
        // inv
        let (inv_num, inv_den) = if num.sign() == Sign::Minus {
            (-BigInt::from(den.clone()), num.magnitude().clone())
        } else if num.sign() == Sign::Plus {
            (BigInt::from(den.clone()), num.magnitude().clone())
        } else {
            (num.clone(), den.clone())
        };
        if inv_num == num && inv_den == den {
            return Ok(Some(expr::apps(a_w, &args[args.len()..])));
        }
        Ok(None)
    }

    fn is_rat_const(&self, e: &Expr) -> bool {
        let (h, _) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) => {
                let s = self.name_str(*n);
                s == "Rat" || s.ends_with(".Rat")
            }
            _ => false,
        }
    }

    fn rat_closed_parts(&self, ctx: &Ctx, e: &Expr) -> R<Option<(BigInt, BigUint, Expr)>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        let ident = name.rsplit('.').next().unwrap_or(name);
        if ident == "mk'" && name.contains("Rat") && args.len() >= 4 {
            let Some(num) = self.closed_int_value(ctx, &args[args.len() - 4])? else {
                return Ok(None);
            };
            let Some(den) = self.closed_nat_value(ctx, &args[args.len() - 3])? else {
                return Ok(None);
            };
            return Ok(Some((num, den, e)));
        }
        if ident == "ofInt" && name.contains("Rat") && !args.is_empty() {
            let Some(num) = self.closed_int_value(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some((num, BigUint::from(1u32), e)));
        }
        if name == "OfNat.ofNat" && args.len() >= 2 && self.is_rat_const(&args[0]) {
            let Some(n) = self.closed_nat_value(ctx, &args[1])? else {
                return Ok(None);
            };
            return Ok(Some((BigInt::from(n), BigUint::from(1u32), e)));
        }
        if ident == "natCast" && args.len() >= 2 && self.is_rat_const(&args[0]) {
            let Some(n) = self.closed_nat_value(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some((BigInt::from(n), BigUint::from(1u32), e)));
        }
        if ident == "intCast" && args.len() >= 2 && self.is_rat_const(&args[0]) {
            let Some(n) = self.closed_int_value(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some((n, BigUint::from(1u32), e)));
        }
        Ok(None)
    }

    fn try_dite(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let is_dite = name == "dite";
        let is_ite = name == "ite";
        if !is_dite && !is_ite {
            return Ok(None);
        }
        if args.len() < 5 {
            return Ok(None);
        }
        let inst = self.whnf(ctx, &args[2])?;
        let (ih, iargs) = expr::unfold_apps(&inst);
        let iname = match &**ih {
            ExprData::Const(cn, _) => self.name_str(*cn),
            _ => return Ok(None),
        };
        let is_true = matches!(iname, "Decidable.isTrue" | "isTrue");
        let is_false = matches!(iname, "Decidable.isFalse" | "isFalse");
        if !is_true && !is_false {
            return Ok(None);
        }
        let proof = match iargs.last() {
            Some(p) => p.clone(),
            None => return Ok(None),
        };
        let branch = if is_true { &args[3] } else { &args[4] };
        let reduced = if is_dite {
            expr::app(branch.clone(), proof)
        } else {
            branch.clone()
        };
        Ok(Some(expr::apps(reduced, &args[5..])))
    }

    fn is_closed_int_list(&self, e: &Expr) -> bool {
        if self.is_list_nil(e) {
            return true;
        }
        if let Some((x, xs)) = self.list_cons_parts(e) {
            return self.is_closed_int_numeral(&x) && self.is_closed_int_list(&xs);
        }
        false
    }

    fn is_list_nil(&self, e: &Expr) -> bool {
        let (h, _) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) => {
                let s = self.name_str(*n);
                s == "List.nil" || s.ends_with(".List.nil")
            }
            _ => false,
        }
    }

    fn list_cons_parts(&self, e: &Expr) -> Option<(Expr, Expr)> {
        let (h, args) = expr::unfold_apps(e);
        let s = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if s != "List.cons" && !s.ends_with(".List.cons") {
            return None;
        }
        // List.cons.{u} α x xs
        if args.len() >= 3 {
            Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
        } else if args.len() >= 2 {
            Some((args[0].clone(), args[1].clone()))
        } else {
            None
        }
    }

    fn int_zero(&self) -> Option<Expr> {
        if let Some(ofnat) = self.find_name("OfNat.ofNat") {
            if let Some(int_ty) = self.find_name_ending("Int") {
                if let Some(inst) = self
                    .find_name("instOfNat")
                    .or_else(|| self.find_name_ending("instOfNatInt"))
                {
                    return Some(expr::apps(
                        expr::const_(ofnat, vec![level::zero()]),
                        &[
                            expr::const_(int_ty, vec![]),
                            expr::lit_nat(0u32.into()),
                            expr::app(expr::const_(inst, vec![]), expr::lit_nat(0u32.into())),
                        ],
                    ));
                }
            }
        }
        Some(expr::lit_nat(0u32.into()))
    }

    /// `IntList`/`Coeffs` list algebra used by omega reflection.
    /// Closed `Int.Linear` poly merge / certificates. `combine_mul_k` is
    /// `Nat.rec hugeFuel` (1e8); peeling it hits the rec cap and Init
    /// `#17742` (`diseq_eq_subst_cert`) cannot reduce to `true`.
    fn try_int_linear(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let ident = name.rsplit('.').next().unwrap_or(name);
        if !name.contains("Int.Linear")
            && !name.contains("RArray")
            && ident != "getElem"
            && !is_int_linear_ident(name, "diseq_eq_subst_cert")
            && !is_int_linear_ident(name, "combine_mul_k")
        {
            return Ok(None);
        }
        let trace = std::env::var_os("KIOTA_TRACE_LINEAR").is_some()
            && (ident == "diseq_eq_subst_cert"
                || ident == "combine_mul_k"
                || ident == "norm_eq_cert"
                || ident == "denote"
                || ident == "denote'"
                || ident == "go"
                || ident == "get");
        if trace {
            eprintln!("LINEAR ident={ident} nargs={} name={name}", args.len());
        }

        if ident == "get" && name.contains("RArray") && args.len() >= 2 {
            let arr = &args[args.len() - 2];
            let idx = &args[args.len() - 1];
            if let Some(r) = self.rarray_get(ctx, arr, idx)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
            return Ok(None);
        }
        if ident == "getElem" && args.len() >= 3 {
            let arr = &args[args.len() - 3];
            let idx = &args[args.len() - 2];
            if let Some(r) = self.rarray_get(ctx, arr, idx)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if ident == "denote" && name.contains("Int.Linear.Var") && args.len() >= 2 {
            let arr = &args[args.len() - 2];
            let idx = args.last().unwrap();
            let got = self.rarray_get(ctx, arr, idx)?;
            if trace {
                let arr_w = self.whnf(ctx, arr)?;
                let (h, as_) = expr::unfold_apps(&arr_w);
                let hn = match &**h {
                    ExprData::Const(cn, _) => self.name_str(*cn),
                    _ => "?",
                };
                eprintln!(
                    "VAR_DENOTE nargs={} got={} arr_head={hn} arr_nargs={} idx={}",
                    args.len(),
                    got.is_some(),
                    as_.len(),
                    self.pp_budget(idx, 12)
                );
            }
            if let Some(r) = got {
                return Ok(Some(r));
            }
            return Ok(None);
        }
        // `Expr.denote` / `Poly.denote'` are semireducible abbrevs whose
        // `+`/`*` become `HAdd`/`HMul`. Unfolding those to `Int.add` and
        // then `Nat.rec` hits the peel cap (`#17844`). Rebuild the same
        // notation spine Lean stores: left-fold `denote'`, original
        // OfNat/Neg numerals, never `Int.add`. `#17809` is `Eq.refl` of
        // that HAdd tree (`eq_def`).
        if ident == "denote" && name.contains("Int.Linear.Expr") && args.len() >= 2 {
            let rctx = &args[args.len() - 2];
            let e = args.last().unwrap();
            if let Some(r) = self.linear_expr_denote(ctx, rctx, e)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if ident == "denote'" && name.contains("Poly") && args.len() >= 2 {
            let rctx = &args[args.len() - 2];
            let p = args.last().unwrap();
            if let Some(r) = self.linear_poly_denote_prime(ctx, rctx, p)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if ident == "go" && name.contains("denote'") && args.len() >= 3 {
            let rctx = &args[args.len() - 3];
            let p = &args[args.len() - 2];
            let acc = args.last().unwrap().clone();
            if let Some(r) = self.linear_poly_denote_go(ctx, rctx, p, acc)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if ident == "combine_mul_k" && args.len() >= 4 {
            let Some(a) = self.closed_int_value(ctx, &self.whnf(ctx, &args[0])?)? else {
                return Ok(None);
            };
            let Some(b) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                return Ok(None);
            };
            let Some(p1) = self.parse_linear_poly(ctx, &args[2])? else {
                return Ok(None);
            };
            let Some(p2) = self.parse_linear_poly(ctx, &args[3])? else {
                return Ok(None);
            };
            let r = LinearPoly::combine_mul_k(&a, &b, &p1, &p2);
            if let Some(e) = self.mk_linear_poly(&r) {
                return Ok(Some(expr::apps(e, &args[4..])));
            }
            return Ok(None);
        }
        if ident == "combine" && args.len() >= 2 && name.contains("Poly") {
            let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                return Ok(None);
            };
            let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                return Ok(None);
            };
            let r = LinearPoly::combine_mul_k(&BigInt::from(1), &BigInt::from(1), &p1, &p2);
            if let Some(e) = self.mk_linear_poly(&r) {
                return Ok(Some(expr::apps(e, &args[2..])));
            }
            return Ok(None);
        }

        let bool_r = match ident {
            "diseq_eq_subst_cert" if args.len() >= 4 => {
                let xw = self.whnf(ctx, &args[0])?;
                let Some(x) = self.closed_nat_value(ctx, &xw)? else {
                    if trace {
                        eprintln!("LINEAR diseq: x not closed {}", self.pp_budget(&xw, 40));
                    }
                    return Ok(None);
                };
                let Some(p1) = self.parse_linear_poly(ctx, &args[1])? else {
                    if trace {
                        eprintln!(
                            "LINEAR diseq: p1 parse fail {}",
                            self.pp_budget(&args[1], 40)
                        );
                    }
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[2])? else {
                    if trace {
                        eprintln!("LINEAR diseq: p2 parse fail");
                    }
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[3])? else {
                    if trace {
                        eprintln!(
                            "LINEAR diseq: p3 parse fail {}",
                            self.pp_budget(&args[3], 40)
                        );
                    }
                    return Ok(None);
                };
                let a = p1.coeff(&x);
                let b = p2.coeff(&x);
                let r = a.sign() != Sign::NoSign
                    && p3.beq(&LinearPoly::combine_mul_k(&b, &(-&a), &p1, &p2));
                if trace {
                    eprintln!("LINEAR diseq: x={x} a={a} b={b} r={r}");
                }
                Some(r)
            }
            "eq_eq_subst_cert" if args.len() >= 4 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p1) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[3])? else {
                    return Ok(None);
                };
                let a = p1.coeff(&x);
                let b = p2.coeff(&x);
                Some(p3.beq(&LinearPoly::combine_mul_k(&b, &(-&a), &p1, &p2)))
            }
            "eq_eq_subst'_cert" if args.len() >= 5 => {
                let Some(a) = self.closed_int_value(ctx, &self.whnf(ctx, &args[0])?)? else {
                    return Ok(None);
                };
                let Some(b) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                    return Ok(None);
                };
                let Some(p1) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[3])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[4])? else {
                    return Ok(None);
                };
                Some(p3.beq(&LinearPoly::combine_mul_k(&b, &(-&a), &p1, &p2)))
            }
            "eq_of_le_ge_cert" if args.len() >= 2 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                Some(p2.beq(&p1.mul(&BigInt::from(-1))))
            }
            "eq_of_core_cert" if args.len() >= 3 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                Some(p3.beq(&LinearPoly::combine_mul_k(
                    &BigInt::from(1),
                    &BigInt::from(-1),
                    &p1,
                    &p2,
                )))
            }
            "le_of_le_diseq_cert" if args.len() >= 3 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let neg = p1.mul(&BigInt::from(-1));
                Some((p2.beq(&p1) || p2.beq(&neg)) && p3.beq(&p1.add_const(&BigInt::from(1))))
            }
            "diseq_split_cert" if args.len() >= 3 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let one = BigInt::from(1);
                Some(
                    p2.beq(&p1.add_const(&one))
                        && p3.beq(&p1.mul(&BigInt::from(-1)).add_const(&one)),
                )
            }
            "le_coeff_cert" if args.len() >= 3 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                Some(k.sign() == Sign::Plus && p1.div_coeffs(&k) && p2.beq(&p1.div(&k)))
            }
            "le_neg_cert" if args.len() >= 2 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                Some(p2.beq(&p1.mul(&BigInt::from(-1)).add_const(&BigInt::from(1))))
            }
            "le_combine_cert" if args.len() >= 3 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let a1 = LinearPoly::nat_abs(&p1.lead_coeff());
                let a2 = LinearPoly::nat_abs(&p2.lead_coeff());
                Some(p3.beq(&LinearPoly::combine_mul_k(&a2, &a1, &p1, &p2)))
            }
            "le_combine_coeff_cert" if args.len() >= 4 => {
                let Some(p1) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[3])?)? else {
                    return Ok(None);
                };
                let a1 = LinearPoly::nat_abs(&p1.lead_coeff());
                let a2 = LinearPoly::nat_abs(&p2.lead_coeff());
                let p = LinearPoly::combine_mul_k(&a2, &a1, &p1, &p2);
                Some(k.sign() == Sign::Plus && p.div_coeffs(&k) && p3.beq(&p.div(&k)))
            }
            "eq_coeff_cert" if args.len() >= 3 => {
                let Some(p) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                Some(p.beq(&p2.mul(&k)) && k.sign() == Sign::Plus)
            }
            "eq_unsat_coeff_cert" if args.len() >= 2 => {
                let Some(p) = self.parse_linear_poly(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                    return Ok(None);
                };
                Some(
                    p.div_coeffs(&k)
                        && k.sign() == Sign::Plus
                        && int_cmod(&p.get_const(), &k).sign() == Sign::Minus,
                )
            }
            "dvd_of_eq_cert" if args.len() >= 4 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p1) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(d2) = self.closed_int_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[3])? else {
                    return Ok(None);
                };
                let a = p1.coeff(&x);
                Some(d2 == LinearPoly::nat_abs(&a) && p2.beq(&p1.insert(&(-&a), &x)))
            }
            "eq_dvd_subst_cert" if args.len() >= 6 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(p1) = self.parse_linear_poly(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(d2) = self.closed_int_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                let Some(p2) = self.parse_linear_poly(ctx, &args[3])? else {
                    return Ok(None);
                };
                let Some(d3) = self.closed_int_value(ctx, &self.whnf(ctx, &args[4])?)? else {
                    return Ok(None);
                };
                let Some(p3) = self.parse_linear_poly(ctx, &args[5])? else {
                    return Ok(None);
                };
                let a = p1.coeff(&x);
                let b = p2.coeff(&x);
                let p = p1.insert(&(-&a), &x);
                let q = p2.insert(&(-&b), &x);
                Some(
                    d3 == LinearPoly::nat_abs(&(&a * &d2))
                        && p3.beq(&LinearPoly::combine_mul_k(&a, &(-&b), &q, &p)),
                )
            }
            "var_eq_cert" if args.len() >= 3 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                    return Ok(None);
                };
                let Some(p) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                Some(match p {
                    LinearPoly::Add(k1, x2, rest) => match *rest {
                        LinearPoly::Num(k2) => {
                            k1.sign() != Sign::NoSign && x == x2 && k == -int_ediv(&k2, &k1)
                        }
                        _ => false,
                    },
                    _ => false,
                })
            }
            "of_var_eq_mul_cert" if args.len() >= 4 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                    return Ok(None);
                };
                let Some(y) = self.closed_nat_value(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(p) = self.parse_linear_poly(ctx, &args[3])? else {
                    return Ok(None);
                };
                let want = LinearPoly::Add(
                    BigInt::from(1),
                    x,
                    Box::new(LinearPoly::Add(
                        -k,
                        y,
                        Box::new(LinearPoly::Num(BigInt::from(0))),
                    )),
                );
                Some(p.beq(&want))
            }
            "of_var_eq_var_cert" if args.len() >= 3 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(y) = self.closed_nat_value(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let want = LinearPoly::Add(
                    BigInt::from(1),
                    x,
                    Box::new(LinearPoly::Add(
                        BigInt::from(-1),
                        y,
                        Box::new(LinearPoly::Num(BigInt::from(0))),
                    )),
                );
                Some(p.beq(&want))
            }
            "norm_eq_cert" if args.len() >= 3 => {
                let trace = std::env::var_os("KIOTA_TRACE_LINEAR").is_some();
                let lhs = self.parse_linear_expr(ctx, &args[0])?;
                let rhs = self.parse_linear_expr(ctx, &args[1])?;
                let p = self.parse_linear_poly(ctx, &args[2])?;
                if trace {
                    eprintln!(
                        "LINEAR norm_eq_cert lhs={} rhs={} p={} a0={}",
                        lhs.is_some(),
                        rhs.is_some(),
                        p.is_some(),
                        self.pp_budget(&args[0], 30)
                    );
                }
                let (Some(lhs), Some(rhs), Some(p)) = (lhs, rhs, p) else {
                    return Ok(None);
                };
                let n = LinearExpr::Sub(Box::new(lhs), Box::new(rhs)).norm();
                let r = p.beq(&n);
                if trace {
                    eprintln!("LINEAR norm_eq_cert beq={r}");
                }
                Some(r)
            }
            "norm_eq_var_cert" if args.len() >= 4 => {
                let Some(lhs) = self.parse_linear_expr(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(rhs) = self.parse_linear_expr(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(x) = self.closed_nat_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                let Some(y) = self.closed_nat_value(ctx, &self.whnf(ctx, &args[3])?)? else {
                    return Ok(None);
                };
                let want = LinearPoly::Add(
                    BigInt::from(1),
                    x,
                    Box::new(LinearPoly::Add(
                        BigInt::from(-1),
                        y,
                        Box::new(LinearPoly::Num(BigInt::from(0))),
                    )),
                );
                Some(
                    LinearExpr::Sub(Box::new(lhs), Box::new(rhs))
                        .norm()
                        .beq(&want),
                )
            }
            "norm_eq_var_const_cert" if args.len() >= 4 => {
                let Some(lhs) = self.parse_linear_expr(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(rhs) = self.parse_linear_expr(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(x) = self.closed_nat_value(ctx, &self.whnf(ctx, &args[2])?)? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[3])?)? else {
                    return Ok(None);
                };
                let want = LinearPoly::Add(BigInt::from(1), x, Box::new(LinearPoly::Num(-k)));
                Some(
                    LinearExpr::Sub(Box::new(lhs), Box::new(rhs))
                        .norm()
                        .beq(&want),
                )
            }
            "norm_eq_coeff_cert" if args.len() >= 4 => {
                let Some(lhs) = self.parse_linear_expr(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(rhs) = self.parse_linear_expr(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(p) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[3])?)? else {
                    return Ok(None);
                };
                let n = LinearExpr::Sub(Box::new(lhs), Box::new(rhs)).norm();
                Some(n.beq(&p.mul(&k)) && k.sign() == Sign::Plus)
            }
            "of_var_eq_cert" if args.len() >= 3 => {
                let Some(x) = self.closed_nat_value(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[1])?)? else {
                    return Ok(None);
                };
                let Some(p) = self.parse_linear_poly(ctx, &args[2])? else {
                    return Ok(None);
                };
                let want = LinearPoly::Add(BigInt::from(1), x, Box::new(LinearPoly::Num(-k)));
                Some(p.beq(&want))
            }
            _ => None,
        };
        if let Some(v) = bool_r {
            if let Some(e) = self.mk_bool_const(v) {
                let skip = match ident {
                    "eq_eq_subst'_cert" => 5,
                    "eq_dvd_subst_cert" => 6,
                    "dvd_of_eq_cert"
                    | "of_var_eq_mul_cert"
                    | "le_combine_coeff_cert"
                    | "norm_eq_var_cert"
                    | "norm_eq_var_const_cert"
                    | "norm_eq_coeff_cert" => 4,
                    "diseq_eq_subst_cert" | "eq_eq_subst_cert" => 4,
                    "eq_of_core_cert"
                    | "le_of_le_diseq_cert"
                    | "diseq_split_cert"
                    | "le_coeff_cert"
                    | "le_combine_cert"
                    | "eq_coeff_cert"
                    | "var_eq_cert"
                    | "of_var_eq_var_cert"
                    | "of_var_eq_cert"
                    | "norm_eq_cert" => 3,
                    "eq_unsat_coeff_cert" | "eq_of_le_ge_cert" | "le_neg_cert" => 2,
                    _ => args.len(),
                };
                let r = expr::apps(e, &args[skip.min(args.len())..]);
                if trace {
                    eprintln!(
                        "LINEAR return ident={ident} skip={skip} nargs={} r={}",
                        args.len(),
                        self.pp_budget(&r, 16)
                    );
                }
                return Ok(Some(r));
            } else if trace {
                eprintln!("LINEAR mk_bool FAIL ident={ident}");
            }
        }
        Ok(None)
    }

    fn mk_int_bin(&self, op: &str, a: Expr, b: Expr) -> Option<Expr> {
        let n = self.find_name_ending(op)?;
        Some(expr::apps(expr::const_(n, vec![]), &[a, b]))
    }

    fn mk_int_un(&self, op: &str, a: Expr) -> Option<Expr> {
        let n = self.find_name_ending(op)?;
        Some(expr::app(expr::const_(n, vec![]), a))
    }

    fn mk_hbinop(
        &self,
        method: &str,
        inst_h: &str,
        inst_int: &str,
        a: Expr,
        b: Expr,
    ) -> Option<Expr> {
        let method_n = self.find_name(method)?;
        let int = self.find_name_ending("Int")?;
        let inst_h_n = self.find_name(inst_h)?;
        let inst_int_n = self.find_name(inst_int)?;
        let z = level::zero();
        let ity = expr::const_(int, vec![]);
        let inst = expr::apps(
            expr::const_(inst_h_n, vec![z.clone()]),
            &[ity.clone(), expr::const_(inst_int_n, vec![])],
        );
        Some(expr::apps(
            expr::const_(method_n, vec![z.clone(), z.clone(), z]),
            &[ity.clone(), ity.clone(), ity, inst, a, b],
        ))
    }

    fn mk_hadd(&self, a: Expr, b: Expr) -> Option<Expr> {
        self.mk_hbinop("HAdd.hAdd", "instHAdd", "Int.instAdd", a, b)
    }

    fn mk_hsub(&self, a: Expr, b: Expr) -> Option<Expr> {
        self.mk_hbinop("HSub.hSub", "instHSub", "Int.instSub", a, b)
    }

    fn mk_hmul(&self, a: Expr, b: Expr) -> Option<Expr> {
        self.mk_hbinop("HMul.hMul", "instHMul", "Int.instMul", a, b)
    }

    fn mk_hneg(&self, a: Expr) -> Option<Expr> {
        let neg = self.find_name("Neg.neg")?;
        let int = self.find_name_ending("Int")?;
        let inst = self
            .find_name("Int.instNegInt")
            .or_else(|| self.find_name_ending("instNegInt"))?;
        let z = level::zero();
        Some(expr::apps(
            expr::const_(neg, vec![z]),
            &[expr::const_(int, vec![]), expr::const_(inst, vec![]), a],
        ))
    }

    fn rarray_get(&self, ctx: &Ctx, arr: &Expr, idx: &Expr) -> R<Option<Expr>> {
        let Some(n) = self.closed_nat_value(ctx, idx)? else {
            return Ok(None);
        };
        let mut cur = self.whnf(ctx, arr)?;
        loop {
            let (h, args) = expr::unfold_apps(&cur);
            let name = match &**h {
                ExprData::Const(cn, _) => self.name_str(*cn),
                _ => return Ok(None),
            };
            let ident = name.rsplit('.').next().unwrap_or(name);
            if ident == "leaf" && !args.is_empty() {
                return Ok(Some(args.last().unwrap().clone()));
            }
            if ident == "branch" && args.len() >= 3 {
                let p = &args[args.len() - 3];
                let l = &args[args.len() - 2];
                let rgt = &args[args.len() - 1];
                let Some(pv) = self.closed_nat_value(ctx, p)? else {
                    return Ok(None);
                };
                cur = self.whnf(ctx, if n < pv { l } else { rgt })?;
                continue;
            }
            return Ok(None);
        }
    }

    fn linear_expr_denote(&self, ctx: &Ctx, rctx: &Expr, e: &Expr) -> R<Option<Expr>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if is_int_linear_ident(name, "Expr.num") && !args.is_empty() {
            return Ok(Some(args.last().unwrap().clone()));
        }
        if is_int_linear_ident(name, "Expr.var") && !args.is_empty() {
            return self.rarray_get(ctx, rctx, args.last().unwrap());
        }
        if is_int_linear_ident(name, "Expr.neg") && !args.is_empty() {
            let Some(a) = self.linear_expr_denote(ctx, rctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(self.mk_hneg(a));
        }
        if is_int_linear_ident(name, "Expr.add") && args.len() >= 2 {
            let Some(a) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(self.mk_hadd(a, b));
        }
        if is_int_linear_ident(name, "Expr.sub") && args.len() >= 2 {
            let Some(a) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(self.mk_hsub(a, b));
        }
        if is_int_linear_ident(name, "Expr.mulL") && args.len() >= 2 {
            let k = args[args.len() - 2].clone();
            let Some(a) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(self.mk_hmul(k, a));
        }
        if is_int_linear_ident(name, "Expr.mulR") && args.len() >= 2 {
            let Some(a) = self.linear_expr_denote(ctx, rctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let k = args[args.len() - 1].clone();
            return Ok(self.mk_hmul(a, k));
        }
        Ok(None)
    }

    /// `Poly.denote'`: left-fold, skip `k==1` mul and `num 0` add, keep
    /// the original numeral terms (`Neg.neg`/`OfNat`, not `negSucc`).
    fn linear_poly_denote_prime(&self, ctx: &Ctx, rctx: &Expr, p: &Expr) -> R<Option<Expr>> {
        let p = self.whnf(ctx, p)?;
        let (h, args) = expr::unfold_apps(&p);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if is_int_linear_ident(name, "Poly.num") && !args.is_empty() {
            return Ok(Some(args.last().unwrap().clone()));
        }
        if is_int_linear_ident(name, "Poly.add") && args.len() >= 3 {
            let k_term = args[args.len() - 3].clone();
            let v_term = &args[args.len() - 2];
            let rest = &args[args.len() - 1];
            let Some(kv) = self.closed_int_value(ctx, &self.whnf(ctx, &k_term)?)? else {
                return Ok(None);
            };
            let Some(var_e) = self.rarray_get(ctx, rctx, v_term)? else {
                return Ok(None);
            };
            let acc = if kv == BigInt::from(1) {
                var_e
            } else {
                let Some(m) = self.mk_hmul(k_term, var_e) else {
                    return Ok(None);
                };
                m
            };
            return self.linear_poly_denote_go(ctx, rctx, rest, acc);
        }
        Ok(None)
    }

    fn linear_poly_denote_go(
        &self,
        ctx: &Ctx,
        rctx: &Expr,
        p: &Expr,
        acc: Expr,
    ) -> R<Option<Expr>> {
        let p = self.whnf(ctx, p)?;
        let (h, args) = expr::unfold_apps(&p);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if is_int_linear_ident(name, "Poly.num") && !args.is_empty() {
            let k_term = args.last().unwrap().clone();
            let Some(kv) = self.closed_int_value(ctx, &self.whnf(ctx, &k_term)?)? else {
                return Ok(None);
            };
            if kv.sign() == Sign::NoSign {
                return Ok(Some(acc));
            }
            return Ok(self.mk_hadd(acc, k_term));
        }
        if is_int_linear_ident(name, "Poly.add") && args.len() >= 3 {
            let k_term = args[args.len() - 3].clone();
            let v_term = &args[args.len() - 2];
            let rest = &args[args.len() - 1];
            let Some(kv) = self.closed_int_value(ctx, &self.whnf(ctx, &k_term)?)? else {
                return Ok(None);
            };
            let Some(var_e) = self.rarray_get(ctx, rctx, v_term)? else {
                return Ok(None);
            };
            let step = if kv == BigInt::from(1) {
                var_e
            } else {
                let Some(m) = self.mk_hmul(k_term, var_e) else {
                    return Ok(None);
                };
                m
            };
            let Some(acc2) = self.mk_hadd(acc, step) else {
                return Ok(None);
            };
            return self.linear_poly_denote_go(ctx, rctx, rest, acc2);
        }
        Ok(None)
    }

    fn parse_linear_expr(&self, ctx: &Ctx, e: &Expr) -> R<Option<LinearExpr>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if is_int_linear_ident(name, "Expr.num") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(k) = self.closed_int_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::Num(k)));
        }
        if is_int_linear_ident(name, "Expr.var") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(x) = self.closed_nat_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::Var(x)));
        }
        if is_int_linear_ident(name, "Expr.neg") && !args.is_empty() {
            let Some(a) = self.parse_linear_expr(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::Neg(Box::new(a))));
        }
        if is_int_linear_ident(name, "Expr.add") && args.len() >= 2 {
            let Some(a) = self.parse_linear_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.parse_linear_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::Add(Box::new(a), Box::new(b))));
        }
        if is_int_linear_ident(name, "Expr.sub") && args.len() >= 2 {
            let Some(a) = self.parse_linear_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.parse_linear_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::Sub(Box::new(a), Box::new(b))));
        }
        if is_int_linear_ident(name, "Expr.mulL") && args.len() >= 2 {
            let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[args.len() - 2])?)?
            else {
                return Ok(None);
            };
            let Some(a) = self.parse_linear_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::MulL(k, Box::new(a))));
        }
        if is_int_linear_ident(name, "Expr.mulR") && args.len() >= 2 {
            let Some(a) = self.parse_linear_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[args.len() - 1])?)?
            else {
                return Ok(None);
            };
            return Ok(Some(LinearExpr::MulR(Box::new(a), k)));
        }
        Ok(None)
    }

    fn parse_linear_poly(&self, ctx: &Ctx, e: &Expr) -> R<Option<LinearPoly>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if std::env::var_os("KIOTA_TRACE_LINEAR").is_some()
            && !is_int_linear_ident(name, "Poly.num")
            && !is_int_linear_ident(name, "Poly.add")
        {
            eprintln!("LINEAR parse miss head={name} nargs={}", args.len());
        }
        if is_int_linear_ident(name, "Poly.num") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(k) = self.closed_int_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(LinearPoly::Num(k)));
        }
        if is_int_linear_ident(name, "Poly.add") && args.len() >= 3 {
            let k = self.whnf(ctx, &args[args.len() - 3])?;
            let v = self.whnf(ctx, &args[args.len() - 2])?;
            let p = &args[args.len() - 1];
            let Some(kv) = self.closed_int_value(ctx, &k)? else {
                return Ok(None);
            };
            let Some(vv) = self.closed_nat_value(ctx, &v)? else {
                return Ok(None);
            };
            let Some(pv) = self.parse_linear_poly(ctx, p)? else {
                return Ok(None);
            };
            return Ok(Some(LinearPoly::Add(kv, vv, Box::new(pv))));
        }
        Ok(None)
    }

    fn mk_linear_poly(&self, p: &LinearPoly) -> Option<Expr> {
        match p {
            LinearPoly::Num(k) => {
                let ctor = self.find_int_linear_ident("Poly.num")?;
                Some(expr::app(
                    expr::const_(ctor, vec![]),
                    self.mk_int_canonical(k)?,
                ))
            }
            LinearPoly::Add(k, v, rest) => {
                let ctor = self.find_int_linear_ident("Poly.add")?;
                let ke = self.mk_int_canonical(k)?;
                let ve = expr::lit_nat(v.clone());
                let pe = self.mk_linear_poly(rest)?;
                Some(expr::apps(expr::const_(ctor, vec![]), &[ke, ve, pe]))
            }
        }
    }

    fn find_int_linear_ident(&self, ident: &str) -> Option<u32> {
        self.names
            .iter()
            .position(|n| is_int_linear_ident(n.as_str(), ident))
            .map(|i| i as u32)
    }

    fn mk_bool_const(&self, v: bool) -> Option<Expr> {
        let tname = if v { "Bool.true" } else { "Bool.false" };
        let bn = self.find_name(tname)?;
        Some(expr::const_(bn, vec![]))
    }

    /// Closed `Lean.Grind.CommRing` certificates. `toPoly_k` / `combine_k`
    /// are `Expr.rec` / `Nat.rec hugeFuel`; peeling them dies at Init
    /// `#17755` (`norm_cnstr_cert`). Do not intercept `Poly.beq'`.
    fn try_comm_ring(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !name.contains("CommRing") {
            return Ok(None);
        }
        let ident = name.rsplit('.').next().unwrap_or(name);
        let bool_r = match ident {
            "norm_cnstr_cert" if args.len() >= 4 => {
                let Some(lhs) = self.parse_commring_expr(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(rhs) = self.parse_commring_expr(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(lhs2) = self.parse_commring_expr(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(rhs2) = self.parse_commring_expr(ctx, &args[3])? else {
                    return Ok(None);
                };
                let Some(p) = CrExpr::Sub(Box::new(rhs), Box::new(lhs)).to_poly() else {
                    return Ok(None);
                };
                let Some(q) = CrExpr::Sub(Box::new(rhs2), Box::new(lhs2)).to_poly() else {
                    return Ok(None);
                };
                Some(p.beq(&q))
            }
            "norm_eq_cert" if args.len() >= 4 && name.contains("CommRing") => {
                let Some(lhs) = self.parse_commring_expr(ctx, &args[0])? else {
                    return Ok(None);
                };
                let Some(rhs) = self.parse_commring_expr(ctx, &args[1])? else {
                    return Ok(None);
                };
                let Some(lhs2) = self.parse_commring_expr(ctx, &args[2])? else {
                    return Ok(None);
                };
                let Some(rhs2) = self.parse_commring_expr(ctx, &args[3])? else {
                    return Ok(None);
                };
                let Some(p) = CrExpr::Sub(Box::new(lhs), Box::new(rhs)).to_poly() else {
                    return Ok(None);
                };
                let Some(q) = CrExpr::Sub(Box::new(lhs2), Box::new(rhs2)).to_poly() else {
                    return Ok(None);
                };
                Some(p.beq(&q))
            }
            _ => None,
        };
        if let Some(v) = bool_r {
            if let Some(e) = self.mk_bool_const(v) {
                return Ok(Some(expr::apps(e, &args[4.min(args.len())..])));
            }
        }
        Ok(None)
    }

    fn parse_commring_expr(&self, ctx: &Ctx, e: &Expr) -> R<Option<CrExpr>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if is_commring_ident(name, "Expr.num") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(k) = self.closed_int_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Num(k)));
        }
        if is_commring_ident(name, "Expr.natCast") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(k) = self.closed_nat_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::NatCast(k)));
        }
        if is_commring_ident(name, "Expr.intCast") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(k) = self.closed_int_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::IntCast(k)));
        }
        if is_commring_ident(name, "Expr.var") && !args.is_empty() {
            let last = self.whnf(ctx, args.last().unwrap())?;
            let Some(x) = self.closed_nat_value(ctx, &last)? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Var(x)));
        }
        if is_commring_ident(name, "Expr.neg") && !args.is_empty() {
            let Some(a) = self.parse_commring_expr(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Neg(Box::new(a))));
        }
        if is_commring_ident(name, "Expr.add") && args.len() >= 2 {
            let Some(a) = self.parse_commring_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.parse_commring_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Add(Box::new(a), Box::new(b))));
        }
        if is_commring_ident(name, "Expr.sub") && args.len() >= 2 {
            let Some(a) = self.parse_commring_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.parse_commring_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Sub(Box::new(a), Box::new(b))));
        }
        if is_commring_ident(name, "Expr.mul") && args.len() >= 2 {
            let Some(a) = self.parse_commring_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let Some(b) = self.parse_commring_expr(ctx, &args[args.len() - 1])? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Mul(Box::new(a), Box::new(b))));
        }
        if is_commring_ident(name, "Expr.pow") && args.len() >= 2 {
            let Some(a) = self.parse_commring_expr(ctx, &args[args.len() - 2])? else {
                return Ok(None);
            };
            let kw = self.whnf(ctx, &args[args.len() - 1])?;
            let Some(k) = self.closed_nat_value(ctx, &kw)? else {
                return Ok(None);
            };
            return Ok(Some(CrExpr::Pow(Box::new(a), k)));
        }
        Ok(None)
    }

    fn try_intlist(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !name.contains("IntList") && !name.contains("Coeffs") {
            return Ok(None);
        }
        let ends = |s: &str| name == s || name.ends_with(&format!(".{s}"));
        if (ends("IntList.sub") || ends("Coeffs.sub")) && args.len() >= 2 {
            let a = self.whnf(ctx, &args[0])?;
            let b = self.whnf(ctx, &args[1])?;
            // Only closed lists. `IntList.sub_eq_add_neg` is ∀ xs ys and
            // needs `xs - ys` to stay a `sub` under binders.
            if self.is_closed_int_list(&a) && self.is_closed_int_list(&b) && self.is_list_nil(&b) {
                return Ok(Some(expr::apps(a, &args[2..])));
            }
            return Ok(None);
        }
        if (ends("IntList.gcd") || ends("Coeffs.gcd")) && !args.is_empty() {
            if let Some(g) = self.closed_int_list_gcd(ctx, &args[0])? {
                return Ok(Some(expr::apps(expr::lit_nat(g), &args[1..])));
            }
        }
        if (ends("IntList.combo") || ends("Coeffs.combo")) && args.len() >= 4 {
            if let Some(r) =
                self.closed_coeffs_combo(ctx, &args[0], &args[1], &args[2], &args[3])?
            {
                return Ok(Some(expr::apps(r, &args[4..])));
            }
        }
        Ok(None)
    }

    fn closed_coeffs_combo(
        &self,
        ctx: &Ctx,
        a: &Expr,
        xs: &Expr,
        b: &Expr,
        ys: &Expr,
    ) -> R<Option<Expr>> {
        let (Some(av), Some(bv)) = (
            self.closed_int_value(ctx, a)?,
            self.closed_int_value(ctx, b)?,
        ) else {
            return Ok(None);
        };
        let (Some(xs), Some(ys)) = (
            self.closed_int_list_values(ctx, xs)?,
            self.closed_int_list_values(ctx, ys)?,
        ) else {
            return Ok(None);
        };
        let n = xs.len().max(ys.len());
        let mut zs = Vec::with_capacity(n);
        for i in 0..n {
            let x = xs.get(i).cloned().unwrap_or_else(|| 0.into());
            let y = ys.get(i).cloned().unwrap_or_else(|| 0.into());
            zs.push(&av * x + &bv * y);
        }
        Ok(self.mk_closed_int_list(&zs))
    }

    fn option_view(&self, e: &Expr) -> Option<Option<Expr>> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if name == "Option.none" || name.ends_with(".Option.none") {
            return Some(None);
        }
        if name == "Option.some" || name.ends_with(".Option.some") {
            return args.last().cloned().map(Some);
        }
        None
    }

    fn constraint_mk_fields(&self, e: &Expr) -> Option<(Expr, Expr)> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if (name == "Constraint.mk" || name.ends_with(".Constraint.mk")) && args.len() >= 2 {
            return Some((args[0].clone(), args[1].clone()));
        }
        None
    }

    fn option_merge_closed(
        &self,
        ctx: &Ctx,
        a: &Expr,
        b: &Expr,
        take_max: bool,
    ) -> R<Option<Expr>> {
        let a = self.whnf(ctx, a)?;
        let b = self.whnf(ctx, b)?;
        match (self.option_view(&a), self.option_view(&b)) {
            (Some(None), Some(None)) => Ok(Some(a)),
            (Some(Some(_)), Some(None)) => Ok(Some(a)),
            (Some(None), Some(Some(_))) => Ok(Some(b)),
            (Some(Some(x)), Some(Some(y))) => {
                let (Some(xv), Some(yv)) = (
                    self.closed_int_value(ctx, &x)?,
                    self.closed_int_value(ctx, &y)?,
                ) else {
                    return Ok(None);
                };
                let pick_a = if take_max { xv >= yv } else { xv <= yv };
                Ok(Some(if pick_a { a } else { b }))
            }
            _ => Ok(None),
        }
    }

    /// `Constraint.combine` on closed `mk`s: `max` of lower bounds, `min` of uppers.
    fn try_omega_constraint(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let ident = name.rsplit('.').next().unwrap_or(name);
        if ident == "tidyConstraint" || ident == "tidyCoeffs" {
            if args.len() >= 2 {
                if let Some((c, xs)) = self.omega_tidy(ctx, &args[0], &args[1])? {
                    let r = if ident == "tidyConstraint" { c } else { xs };
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
            }
            return Ok(None);
        }
        if !name.contains("Constraint") {
            return Ok(None);
        }
        let ends = |s: &str| name == s || name.ends_with(&format!(".{s}"));
        if ends("Constraint.combine") && args.len() >= 2 {
            let a = self.whnf(ctx, &args[0])?;
            let b = self.whnf(ctx, &args[1])?;
            let Some((alo, ahi)) = self.constraint_mk_fields(&a) else {
                return Ok(None);
            };
            let Some((blo, bhi)) = self.constraint_mk_fields(&b) else {
                return Ok(None);
            };
            let Some(lo) = self.option_merge_closed(ctx, &alo, &blo, true)? else {
                return Ok(None);
            };
            let Some(hi) = self.option_merge_closed(ctx, &ahi, &bhi, false)? else {
                return Ok(None);
            };
            let Some(mk) = self.find_name_ending("Constraint.mk") else {
                return Ok(None);
            };
            let mked = expr::apps(expr::const_(mk, vec![]), &[lo, hi]);
            return Ok(Some(expr::apps(mked, &args[2..])));
        }
        if ends("Constraint.combo") && args.len() >= 4 {
            if let Some(r) =
                self.closed_constraint_combo(ctx, &args[0], &args[1], &args[2], &args[3])?
            {
                return Ok(Some(expr::apps(r, &args[4..])));
            }
        }
        Ok(None)
    }

    /// `Lean.Omega.tidy`: positivize (flip+neg if leading coeff < 0) then
    /// normalize (divide by gcd). Init `#20467` (`ToInt.Add Int64`) is
    /// `Eq.refl true` after `tidyConstraint`/`tidyCoeffs` of
    /// `mk (some -(2^63-1)) (some 2^64-1)` with coeffs `[0,0,-2^64,2^64]`.
    fn omega_tidy(&self, ctx: &Ctx, s: &Expr, x: &Expr) -> R<Option<(Expr, Expr)>> {
        let s = self.whnf(ctx, s)?;
        let Some((lo_e, hi_e)) = self.constraint_mk_fields(&s) else {
            return Ok(None);
        };
        let Some(mut lo) = self.closed_option_int(ctx, &lo_e)? else {
            return Ok(None);
        };
        let Some(mut hi) = self.closed_option_int(ctx, &hi_e)? else {
            return Ok(None);
        };
        let Some(mut coeffs) = self.closed_int_list_values(ctx, x)? else {
            return Ok(None);
        };
        let leading = coeffs
            .iter()
            .find(|c| c.sign() != Sign::NoSign)
            .cloned()
            .unwrap_or_else(|| BigInt::from(0));
        if leading.sign() == Sign::Minus {
            let new_lo = hi.as_ref().map(|h| -h);
            let new_hi = lo.as_ref().map(|l| -l);
            lo = new_lo;
            hi = new_hi;
            for c in &mut coeffs {
                *c = -&*c;
            }
        }
        let mut g = BigUint::from(0u32);
        for c in &coeffs {
            let abs = c.magnitude().clone();
            g = if g == BigUint::from(0u32) {
                abs
            } else {
                num_bigint_gcd(&g, &abs)
            };
        }
        if g == BigUint::from(0u32) {
            let sat0 = lo.as_ref().map(|l| l <= &BigInt::from(0)).unwrap_or(true)
                && hi.as_ref().map(|h| &BigInt::from(0) <= h).unwrap_or(true);
            if sat0 {
                lo = None;
                hi = None;
            } else {
                lo = Some(BigInt::from(1));
                hi = Some(BigInt::from(0));
            }
        } else if g != BigUint::from(1u32) {
            let gk = BigInt::from(g.clone());
            lo = lo.map(|x| -int_ediv(&(-&x), &gk));
            hi = hi.map(|y| int_ediv(&y, &gk));
            coeffs = coeffs.iter().map(|x| int_ediv(x, &gk)).collect();
        }
        let Some(mk) = self.find_name_ending("Constraint.mk") else {
            return Ok(None);
        };
        let Some(lo_e) = self.mk_option_int(lo) else {
            return Ok(None);
        };
        let Some(hi_e) = self.mk_option_int(hi) else {
            return Ok(None);
        };
        let c = expr::apps(expr::const_(mk, vec![]), &[lo_e, hi_e]);
        let Some(xs) = self.mk_closed_int_list(&coeffs) else {
            return Ok(None);
        };
        Ok(Some((c, xs)))
    }

    fn closed_option_int(&self, ctx: &Ctx, e: &Expr) -> R<Option<Option<num_bigint::BigInt>>> {
        let e = self.whnf(ctx, e)?;
        match self.option_view(&e) {
            Some(None) => Ok(Some(None)),
            Some(Some(x)) => Ok(self.closed_int_value(ctx, &x)?.map(Some)),
            None => Ok(None),
        }
    }

    fn mk_option_int(&self, v: Option<num_bigint::BigInt>) -> Option<Expr> {
        let int_ty = expr::const_(self.find_name_ending("Int")?, vec![]);
        match v {
            None => {
                let none = self.find_name("Option.none")?;
                Some(expr::app(expr::const_(none, vec![level::zero()]), int_ty))
            }
            Some(n) => {
                let some = self.find_name("Option.some")?;
                let x = self.mk_closed_int(&n)?;
                Some(expr::apps(
                    expr::const_(some, vec![level::zero()]),
                    &[int_ty, x],
                ))
            }
        }
    }

    fn scale_constraint_bounds(
        k: &num_bigint::BigInt,
        lo: Option<num_bigint::BigInt>,
        hi: Option<num_bigint::BigInt>,
    ) -> (Option<num_bigint::BigInt>, Option<num_bigint::BigInt>) {
        if k == &0.into() {
            if let (Some(l), Some(h)) = (&lo, &hi) {
                if h < l {
                    return (lo, hi);
                }
            }
            return (Some(0.into()), Some(0.into()));
        }
        if k > &0.into() {
            (lo.map(|x| k * x), hi.map(|x| k * x))
        } else {
            (hi.map(|x| k * x), lo.map(|x| k * x))
        }
    }

    fn closed_constraint_combo(
        &self,
        ctx: &Ctx,
        a: &Expr,
        x: &Expr,
        b: &Expr,
        y: &Expr,
    ) -> R<Option<Expr>> {
        let (Some(av), Some(bv)) = (
            self.closed_int_value(ctx, a)?,
            self.closed_int_value(ctx, b)?,
        ) else {
            return Ok(None);
        };
        let x = self.whnf(ctx, x)?;
        let y = self.whnf(ctx, y)?;
        let Some((xlo, xhi)) = self.constraint_mk_fields(&x) else {
            return Ok(None);
        };
        let Some((ylo, yhi)) = self.constraint_mk_fields(&y) else {
            return Ok(None);
        };
        let (Some(xlo), Some(xhi), Some(ylo), Some(yhi)) = (
            self.closed_option_int(ctx, &xlo)?,
            self.closed_option_int(ctx, &xhi)?,
            self.closed_option_int(ctx, &ylo)?,
            self.closed_option_int(ctx, &yhi)?,
        ) else {
            return Ok(None);
        };
        let (slo, shi) = Self::scale_constraint_bounds(&av, xlo, xhi);
        let (tlo, thi) = Self::scale_constraint_bounds(&bv, ylo, yhi);
        let lo = match (slo, tlo) {
            (Some(p), Some(q)) => Some(p + q),
            _ => None,
        };
        let hi = match (shi, thi) {
            (Some(p), Some(q)) => Some(p + q),
            _ => None,
        };
        let Some(mk) = self.find_name_ending("Constraint.mk") else {
            return Ok(None);
        };
        let Some(lo_e) = self.mk_option_int(lo) else {
            return Ok(None);
        };
        let Some(hi_e) = self.mk_option_int(hi) else {
            return Ok(None);
        };
        Ok(Some(expr::apps(expr::const_(mk, vec![]), &[lo_e, hi_e])))
    }

    fn find_name(&self, s: &str) -> Option<u32> {
        self.names
            .iter()
            .position(|n| n.as_str() == s)
            .map(|i| i as u32)
    }

    fn is_closed_int_numeral(&self, e: &Expr) -> bool {
        if let ExprData::Lit(Lit::Nat(_)) = &***e {
            return true;
        }
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return false,
        };
        if name == "OfNat.ofNat" && args.len() >= 2 {
            return matches!(&**args[1], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.ofNat" || name.ends_with(".Int.ofNat") {
            return !args.is_empty() && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.negSucc" || name.ends_with(".Int.negSucc") {
            return !args.is_empty() && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.neg" || name.ends_with(".Int.neg") || name == "Neg.neg" {
            return args.last().is_some_and(|a| self.is_closed_int_numeral(a));
        }
        false
    }

    /// `Int.neg x` or `Neg.neg Int _ x` → `x`. Used only to cancel a
    /// second closed negation (`- - n = n`); open `n` must stay a `neg`
    /// so `Int.neg_neg` still matches its recursor motive.
    fn peel_int_neg(&self, e: &Expr) -> Option<Expr> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if name == "Int.neg" || name.ends_with(".Int.neg") {
            return args.first().cloned();
        }
        if name == "Neg.neg" && args.len() >= 3 {
            return Some(args[2].clone());
        }
        None
    }

    fn closed_nat_value(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigUint>> {
        let a = self.reduce_nat_arg(ctx, e)?;
        if let Some(v) = nat::as_lit(&a) {
            return Ok(Some(v.clone()));
        }
        if let Some((zero, succ)) = self.nat_ctors() {
            if let Some(v) = nat::numeral_value(&a, zero, succ) {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    /// Closed `Int` numerals only. Open terms (e.g. `0 - n`) stay untouched
    /// so lemmas like `Int.zero_sub` still see a `sub`.
    fn closed_int_value(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigInt>> {
        if let ExprData::Lit(Lit::Nat(n)) = &***e {
            return Ok(Some(BigInt::from(n.clone())));
        }
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if name == "OfNat.ofNat" && args.len() >= 2 {
            if let Some(n) = self.closed_nat_value(ctx, &args[1])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if name == "Int.ofNat" || name.ends_with(".Int.ofNat") {
            if let Some(n) = args.first() {
                if let Some(v) = self.closed_nat_value(ctx, n)? {
                    return Ok(Some(BigInt::from(v)));
                }
            }
            return Ok(None);
        }
        if name == "Int.negSucc" || name.ends_with(".Int.negSucc") {
            if let Some(n) = args.first() {
                if let Some(v) = self.closed_nat_value(ctx, n)? {
                    return Ok(Some(-BigInt::from(v) - 1));
                }
            }
            return Ok(None);
        }
        if name == "Int.neg" || name.ends_with(".Int.neg") {
            if let Some(a) = args.first() {
                if let Some(v) = self.closed_int_value(ctx, a)? {
                    return Ok(Some(-v));
                }
            }
            return Ok(None);
        }
        if name == "Neg.neg" && args.len() >= 3 {
            if let Some(v) = self.closed_int_value(ctx, &args[2])? {
                return Ok(Some(-v));
            }
            return Ok(None);
        }
        if (name == "Int.ediv" || name.ends_with(".Int.ediv") || name == "Int.div")
            && args.len() >= 2
        {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_int_value(ctx, &args[1])?,
            ) {
                return Ok(Some(int_ediv(&a, &b)));
            }
            return Ok(None);
        }
        if name == "HDiv.hDiv" && args.len() >= 6 {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[4])?,
                self.closed_int_value(ctx, &args[5])?,
            ) {
                return Ok(Some(int_ediv(&a, &b)));
            }
            return Ok(None);
        }
        if (name == "Nat.cast" || name == "NatCast.natCast") && args.len() >= 3 {
            if let Some(n) = self.closed_nat_value(ctx, &args[2])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if name == "NatCast.natCast" && args.len() >= 2 {
            if let Some(n) = self.closed_nat_value(ctx, &args[1])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if (name == "Int.pow" || name.ends_with(".Int.pow")) && args.len() >= 2 {
            if let (Some(a), Some(e)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_nat_value(ctx, &args[1])?,
            ) {
                return Ok(int_pow(&a, &e));
            }
            return Ok(None);
        }
        if name == "HPow.hPow" && args.len() >= 6 {
            if let (Some(a), Some(e)) = (
                self.closed_int_value(ctx, &args[4])?,
                self.closed_nat_value(ctx, &args[5])?,
            ) {
                return Ok(int_pow(&a, &e));
            }
            return Ok(None);
        }
        if (name == "Int.bmod" || name.ends_with(".Int.bmod")) && args.len() >= 2 {
            if let (Some(x), Some(m)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_nat_value(ctx, &args[1])?,
            ) {
                return Ok(Some(int_bmod(&x, &m)));
            }
            return Ok(None);
        }
        // std #10980: `Int.decLe 0 (-(10^9-1)+10^9)` — `decide` of that
        // closed inequality is `true`, so `Eq.refl true` matches.
        if (name == "Int.add"
            || name.ends_with(".Int.add")
            || name == "Int.sub"
            || name.ends_with(".Int.sub")
            || name == "Int.mul"
            || name.ends_with(".Int.mul"))
            && args.len() >= 2
        {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_int_value(ctx, &args[1])?,
            ) {
                return Ok(Some(if name.ends_with(".add") || name == "Int.add" {
                    a + b
                } else if name.ends_with(".sub") || name == "Int.sub" {
                    a - b
                } else {
                    a * b
                }));
            }
            return Ok(None);
        }
        if (name == "HAdd.hAdd" || name == "HSub.hSub" || name == "HMul.hMul") && args.len() >= 6 {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[4])?,
                self.closed_int_value(ctx, &args[5])?,
            ) {
                return Ok(Some(match name {
                    "HAdd.hAdd" => a + b,
                    "HSub.hSub" => a - b,
                    _ => a * b,
                }));
            }
            return Ok(None);
        }
        if (name == "Add.add" || name == "Sub.sub" || name == "Mul.mul") && args.len() >= 4 {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[2])?,
                self.closed_int_value(ctx, &args[3])?,
            ) {
                return Ok(Some(match name {
                    "Add.add" => a + b,
                    "Sub.sub" => a - b,
                    _ => a * b,
                }));
            }
            return Ok(None);
        }
        Ok(None)
    }

    /// `Int.ofNat n` / `Int.negSucc (n-1)` — already WHNF, so `Int.neg`
    /// of a closed numeral cannot unfold into a `Nat.rec` of size `n`.
    fn mk_int_canonical(&self, v: &BigInt) -> Option<Expr> {
        if v.sign() != Sign::Minus {
            let ofn = self.find_name_ending("Int.ofNat")?;
            return Some(expr::app(
                expr::const_(ofn, vec![]),
                nat::mk_lit(v.magnitude().clone()),
            ));
        }
        let ns = self.find_name_ending("Int.negSucc")?;
        let mag = v.magnitude();
        if *mag == BigUint::from(0u32) {
            return None;
        }
        Some(expr::app(expr::const_(ns, vec![]), nat::mk_lit(mag - 1u32)))
    }

    /// Kernel-native `Int.decLe`/`Int.decLt` result. The proof payload is
    /// `True.intro`; `ite`/`decide` only inspect the constructor.
    fn mk_decidable_bool(&self, yes: bool) -> Option<Expr> {
        let ctor = if yes {
            "Decidable.isTrue"
        } else {
            "Decidable.isFalse"
        };
        let c = self
            .find_name(ctor)
            .or_else(|| self.find_name_ending(if yes { "isTrue" } else { "isFalse" }))?;
        let true_ty = self.find_name("True")?;
        let intro = self.find_name("True.intro")?;
        Some(expr::apps(
            expr::const_(c, vec![level::zero()]),
            &[expr::const_(true_ty, vec![]), expr::const_(intro, vec![])],
        ))
    }

    fn mk_closed_int(&self, v: &BigInt) -> Option<Expr> {
        if v.sign() == Sign::Minus {
            let pos = self.mk_closed_int(&-v)?;
            let ineg = self.find_name_ending("Int.neg")?;
            return Some(expr::app(expr::const_(ineg, vec![]), pos));
        }
        let n: BigUint = v.magnitude().clone();
        let ofnat = self.find_name("OfNat.ofNat")?;
        let int_ty = self.find_name_ending("Int")?;
        let inst = self
            .find_name("instOfNat")
            .or_else(|| self.find_name_ending("instOfNatInt"))?;
        let lit = expr::lit_nat(n);
        Some(expr::apps(
            expr::const_(ofnat, vec![level::zero()]),
            &[
                expr::const_(int_ty, vec![]),
                lit.clone(),
                expr::app(expr::const_(inst, vec![]), lit),
            ],
        ))
    }

    fn closed_int_list_gcd(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigUint>> {
        let mut cur = self.whnf(ctx, e)?;
        let mut g = BigUint::from(0u32);
        loop {
            if self.is_list_nil(&cur) {
                return Ok(Some(g));
            }
            let Some((x, xs)) = self.list_cons_parts(&cur) else {
                return Ok(None);
            };
            let Some(v) = self.closed_int_value(ctx, &x)? else {
                return Ok(None);
            };
            let abs = v.magnitude().clone();
            g = if g == BigUint::from(0u32) {
                abs
            } else {
                num_bigint_gcd(&g, &abs)
            };
            cur = self.whnf(ctx, &xs)?;
        }
    }

    fn is_int_of_nat_zero(&self, e: &Expr) -> bool {
        if let ExprData::Lit(Lit::Nat(n)) = &***e {
            return *n == num_bigint::BigUint::from(0u32);
        }
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return false,
        };
        if name == "OfNat.ofNat" && args.len() >= 2 {
            if let ExprData::Lit(Lit::Nat(n)) = &**args[1] {
                return *n == num_bigint::BigUint::from(0u32);
            }
        }
        if (name == "Int.ofNat" || name.ends_with(".Int.ofNat")) && !args.is_empty() {
            if let ExprData::Lit(Lit::Nat(n)) = &**args[0] {
                return *n == num_bigint::BigUint::from(0u32);
            }
        }
        false
    }

    fn find_name_ending(&self, suffix: &str) -> Option<u32> {
        self.names
            .iter()
            .position(|n| {
                let s = n.as_str();
                s == suffix || s.ends_with(&format!(".{suffix}"))
            })
            .map(|i| i as u32)
    }

    fn linear_combo_mk_parts(&self, e: &Expr) -> Option<(Expr, Expr)> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if (name == "LinearCombo.mk" || name.ends_with(".LinearCombo.mk")) && args.len() >= 2 {
            Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
        } else {
            None
        }
    }

    fn closed_int_list_values(&self, ctx: &Ctx, e: &Expr) -> R<Option<Vec<num_bigint::BigInt>>> {
        let mut cur = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&cur);
        if let ExprData::Const(n, _) = &**h {
            let name = self.name_str(*n);
            if name.contains("ofList") && !args.is_empty() {
                cur = self.whnf(ctx, args.last().unwrap())?;
            }
        }
        let mut out = Vec::new();
        loop {
            if self.is_list_nil(&cur) {
                return Ok(Some(out));
            }
            let Some((x, xs)) = self.list_cons_parts(&cur) else {
                return Ok(None);
            };
            let Some(v) = self.closed_int_value(ctx, &x)? else {
                return Ok(None);
            };
            out.push(v);
            cur = self.whnf(ctx, &xs)?;
        }
    }

    fn mk_closed_int_list(&self, vs: &[num_bigint::BigInt]) -> Option<Expr> {
        let int_ty = self.find_name_ending("Int")?;
        let nil = self.find_name("List.nil")?;
        let cons = self.find_name("List.cons")?;
        let ty = expr::const_(int_ty, vec![]);
        let mut list = expr::app(expr::const_(nil, vec![level::zero()]), ty.clone());
        for v in vs.iter().rev() {
            let x = self.mk_closed_int(v)?;
            list = expr::apps(
                expr::const_(cons, vec![level::zero()]),
                &[ty.clone(), x, list],
            );
        }
        Some(list)
    }

    /// Closed `mk c₁ cs₁ ± mk c₂ cs₂` → `mk (c₁±c₂) (cs₁ ± cs₂)`.
    /// `assemble₃` omega compares `eval (mk 0 [4096,64,1])` with
    /// `eval ((mk 0 [4096]) + (mk 0 [0,64,1]))`.
    fn closed_linear_combo_add_sub(
        &self,
        ctx: &Ctx,
        a: &Expr,
        b: &Expr,
        is_sub: bool,
    ) -> R<Option<Expr>> {
        let Some((c1, cs1)) = self.linear_combo_mk_parts(a) else {
            return Ok(None);
        };
        let Some((c2, cs2)) = self.linear_combo_mk_parts(b) else {
            return Ok(None);
        };
        let (Some(k1), Some(k2)) = (
            self.closed_int_value(ctx, &c1)?,
            self.closed_int_value(ctx, &c2)?,
        ) else {
            return Ok(None);
        };
        let (Some(xs), Some(ys)) = (
            self.closed_int_list_values(ctx, &cs1)?,
            self.closed_int_list_values(ctx, &cs2)?,
        ) else {
            return Ok(None);
        };
        let k = if is_sub { k1 - k2 } else { k1 + k2 };
        let n = xs.len().max(ys.len());
        let mut zs = Vec::with_capacity(n);
        for i in 0..n {
            let x = xs.get(i).cloned().unwrap_or_else(|| 0.into());
            let y = ys.get(i).cloned().unwrap_or_else(|| 0.into());
            zs.push(if is_sub { x - y } else { x + y });
        }
        let Some(mk) = self.find_name_ending("LinearCombo.mk") else {
            return Ok(None);
        };
        let Some(ck) = self.mk_closed_int(&k) else {
            return Ok(None);
        };
        let Some(cl) = self.mk_closed_int_list(&zs) else {
            return Ok(None);
        };
        Ok(Some(expr::apps(expr::const_(mk, vec![]), &[ck, cl])))
    }

    /// Reduce Lean.Omega.LinearCombo eval/add/sub so omega reflection
    /// proofs (e.g. utf8DecodeChar assemble) can see `eval (a - b)` as
    /// `a.const - b.const + dot …`.
    fn try_omega_combo(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !name.contains("LinearCombo") {
            return Ok(None);
        }
        let ends = |s: &str| name == s || name.ends_with(&format!(".{s}"));
        let Some(combo) = self.find_name_ending("LinearCombo") else {
            return Ok(None);
        };
        if ends("LinearCombo.eval") && args.len() >= 2 {
            let lc = self.whnf(ctx, &args[0])?;
            let values = args[1].clone();
            let (lhead, largs) = expr::unfold_apps(&lc);
            let lname = match &**lhead {
                ExprData::Const(cn, _) => self.name_str(*cn).to_string(),
                ExprData::Proj(s, i, _) => {
                    format!("proj:{}.{}", self.name_str(*s), i)
                }
                _ => format!("head:{}", self.pp_budget(&lhead, 20)),
            };
            let (cnst, coeffs) = if (lname == "LinearCombo.mk"
                || lname.ends_with(".LinearCombo.mk"))
                && largs.len() >= 2
            {
                (largs[0].clone(), largs[1].clone())
            } else {
                (expr::proj(combo, 0, lc.clone()), expr::proj(combo, 1, lc))
            };
            let coeffs_w = self.whnf(ctx, &coeffs)?;
            if self.is_list_nil(&coeffs_w) {
                return Ok(Some(expr::apps(cnst, &args[2..])));
            }
            let dot = self.find_name_ending("Coeffs.dot");
            let iadd = self.find_name_ending("Int.add");
            if std::env::var_os("KIOTA_TRACE_OMEGA").is_some() {
                eprintln!(
                    "OMEGA eval nargs={} lname={lname} nargs_lc={} dot={} iadd={} cnst={} coeffs={}",
                    args.len(),
                    largs.len(),
                    dot.is_some(),
                    iadd.is_some(),
                    self.pp_budget(&cnst, 28),
                    self.pp_budget(&coeffs, 28),
                );
            }
            let Some(dot) = dot else {
                return Ok(None);
            };
            let dotted = expr::apps(expr::const_(dot, vec![]), &[coeffs, values]);
            let Some(iadd) = iadd else {
                return Ok(None);
            };
            let sum = expr::apps(expr::const_(iadd, vec![]), &[cnst, dotted]);
            return Ok(Some(expr::apps(sum, &args[2..])));
        }
        if (ends("LinearCombo.sub") || ends("LinearCombo.add")) && args.len() >= 2 {
            let is_sub = ends("LinearCombo.sub");
            let a = self.whnf(ctx, &args[0])?;
            let b = self.whnf(ctx, &args[1])?;
            if let Some(r) = self.closed_linear_combo_add_sub(ctx, &a, &b, is_sub)? {
                return Ok(Some(expr::apps(r, &args[2..])));
            }
            let Some(mk) = self.find_name_ending("LinearCombo.mk") else {
                return Ok(None);
            };
            let ac = expr::proj(combo, 0, a.clone());
            let bc = expr::proj(combo, 0, b.clone());
            let aco = expr::proj(combo, 1, a);
            let bco = expr::proj(combo, 1, b);
            let (const_, coeffs) = if ends("LinearCombo.sub") {
                let Some(isub) = self.find_name_ending("Int.sub") else {
                    return Ok(None);
                };
                let csub = self
                    .find_name_ending("Coeffs.sub")
                    .or_else(|| self.find_name_ending("IntList.sub"));
                let coeffs = if let Some(csub) = csub {
                    expr::apps(expr::const_(csub, vec![]), &[aco, bco])
                } else if let Some(hsub) = self.find_name_ending("HSub.hSub") {
                    expr::apps(expr::const_(hsub, vec![]), &[aco, bco])
                } else {
                    return Ok(None);
                };
                (expr::apps(expr::const_(isub, vec![]), &[ac, bc]), coeffs)
            } else {
                let Some(iadd) = self.find_name_ending("Int.add") else {
                    return Ok(None);
                };
                let cadd = self
                    .find_name_ending("Coeffs.add")
                    .or_else(|| self.find_name_ending("IntList.add"));
                let coeffs = if let Some(cadd) = cadd {
                    expr::apps(expr::const_(cadd, vec![]), &[aco, bco])
                } else if let Some(hadd) = self.find_name_ending("HAdd.hAdd") {
                    expr::apps(expr::const_(hadd, vec![]), &[aco, bco])
                } else {
                    return Ok(None);
                };
                (expr::apps(expr::const_(iadd, vec![]), &[ac, bc]), coeffs)
            };
            let mked = expr::apps(expr::const_(mk, vec![]), &[const_, coeffs]);
            return Ok(Some(expr::apps(mked, &args[2..])));
        }
        Ok(None)
    }

    fn string_to_byte_array(&self, s: &str) -> Option<Expr> {
        let ba_mk = self.find_name("ByteArray.mk")?;
        let arr_mk = self.find_name("Array.mk")?;
        let uint8 = self.find_name("UInt8")?;
        let list_nil = self.find_name("List.nil")?;
        let list_cons = self.find_name("List.cons")?;
        let uint8_ty = expr::const_(uint8, vec![]);
        let mut list = expr::app(
            expr::const_(list_nil, vec![level::zero()]),
            uint8_ty.clone(),
        );
        let u8_of_nat = self.find_name("UInt8.ofNat");
        for b in s.as_bytes().iter().rev() {
            let nat_lit = expr::lit_nat(num_bigint::BigUint::from(*b));
            let uint8_val = if let Some(uon) = u8_of_nat {
                expr::app(expr::const_(uon, vec![]), nat_lit)
            } else {
                nat_lit
            };
            list = expr::apps(
                expr::const_(list_cons, vec![level::zero()]),
                &[uint8_ty.clone(), uint8_val, list],
            );
        }
        let arr = expr::apps(expr::const_(arr_mk, vec![level::zero()]), &[uint8_ty, list]);
        let ba = expr::app(expr::const_(ba_mk, vec![]), arr);
        Some(ba)
    }

    // ---------------- Inductive/recursor validation ----------------

    pub fn check_inductive_group(&self, first_name: u32) -> R<()> {
        let ci = self
            .env
            .get(first_name)
            .ok_or_else(|| TcError::Other("missing inductive".into()))?;
        let (typ, num_params, all, shared_lp) = match ci {
            ConstantInfo::InductiveType {
                typ,
                num_params,
                all,
                level_params,
                ..
            } => (typ.clone(), *num_params, all.clone(), level_params.clone()),
            _ => return Ok(()),
        };
        {
            let mut seen: Vec<u32> = Vec::new();
            for p in &shared_lp {
                if seen.contains(p) {
                    return reject("inductive type: duplicate universe parameter");
                }
                seen.push(*p);
            }
        }
        // Shared parameter telescope, taken from the first type's arity.
        let mut param_ctx: Ctx = Ctx::new();
        let mut cur = typ.clone();
        for _ in 0..num_params {
            let (_, dom, body) = self.ensure_pi(&param_ctx, &cur)?;
            param_ctx.push(dom);
            cur = body;
        }

        struct TInfo {
            num_params: u32,
            num_indices: u32,
            sort: Level,
        }
        let mut infos: FxHashMap<u32, TInfo> = FxHashMap::default();
        for tname in &all {
            let (t_np, t_ni, t_typ, t_lp) = match self.env.get(*tname) {
                Some(ConstantInfo::InductiveType {
                    num_params,
                    num_indices,
                    typ,
                    level_params,
                    ..
                }) => (*num_params, *num_indices, typ.clone(), level_params.clone()),
                _ => continue,
            };
            if t_np != num_params {
                return reject("inconsistent numParams across mutual inductive group");
            }
            if t_lp != shared_lp {
                return reject("inconsistent universe parameters across mutual inductive group");
            }
            let mut c2: Ctx = Ctx::new();
            let mut cur2 = t_typ.clone();
            for i in 0..t_np {
                let (_, dom, body) = self.ensure_pi(&c2, &cur2)?;
                if !self.is_def_eq(&c2, &dom, &param_ctx[i as usize])? {
                    return reject("inductive type's parameter telescope is inconsistent");
                }
                c2.push(dom);
                cur2 = body;
            }
            for _ in 0..t_ni {
                let (_, dom, body) = self.ensure_pi(&c2, &cur2)?;
                c2.push(dom);
                cur2 = body;
            }
            let sort_lvl = self.ensure_sort(&c2, &cur2)?;
            infos.insert(
                *tname,
                TInfo {
                    num_params: t_np,
                    num_indices: t_ni,
                    sort: sort_lvl,
                },
            );
        }

        for tname in &all {
            let ctors = match self.env.get(*tname) {
                Some(ConstantInfo::InductiveType { ctors, .. }) => ctors.clone(),
                _ => continue,
            };
            let t_sort = infos
                .get(tname)
                .map(|i| i.sort.clone())
                .unwrap_or_else(level::zero);
            for cname in &ctors {
                let (c_lp, c_typ, c_np) = match self.env.get(*cname) {
                    Some(ConstantInfo::Constructor {
                        level_params,
                        typ,
                        num_params,
                        ..
                    }) => (level_params.clone(), typ.clone(), *num_params),
                    _ => continue,
                };
                if c_lp != shared_lp {
                    return reject("constructor universe parameters do not match inductive type");
                }
                if c_np != num_params {
                    return reject("constructor numParams does not match inductive type");
                }
                let mut c2: Ctx = Ctx::new();
                let mut cur2 = c_typ.clone();
                for i in 0..num_params {
                    let (_, dom, body) = self.ensure_pi(&c2, &cur2)?;
                    if !self.is_def_eq(&c2, &dom, &param_ctx[i as usize])? {
                        return reject(
                            "constructor parameter telescope does not match inductive type",
                        );
                    }
                    c2.push(dom);
                    cur2 = body;
                }
                loop {
                    // Only walk *manifest* Pis — do not whnf the constructor type
                    // itself (see tutorial/054_reduceCtorType).
                    match &**cur2 {
                        ExprData::Pi(_, dom, body) => {
                            self.check_arg_positive(&c2, dom, &all, num_params)?;
                            let ds = self.infer_type(&c2, dom)?;
                            if let Ok(field_lvl) = self.ensure_sort(&c2, &ds) {
                                // Only reject when both universes are closed numerals;
                                // parametric comparisons are left to `leq`, but a failed
                                // `leq` on open levels is treated as "not sure" to avoid
                                // rejecting valid polymorphic structures such as `HAdd`.
                                if Self::is_closed_numeral(&field_lvl)
                                    && Self::is_closed_numeral(&t_sort)
                                    && !level::leq(&field_lvl, &t_sort, 0)
                                    && !level::is_def_eq(&t_sort, &level::zero())
                                {
                                    return reject("constructor field universe is too big for the inductive type");
                                }
                            }
                            c2.push(dom.clone());
                            cur2 = body.clone();
                        }
                        _ => break,
                    }
                }
                let (head, args) = expr::unfold_apps(&cur2);
                match &**head {
                    ExprData::Const(n, us) if n == tname => {
                        let expected: Vec<Level> =
                            shared_lp.iter().map(|p| level::param(*p)).collect();
                        if us.len() != expected.len()
                            || !us
                                .iter()
                                .zip(expected.iter())
                                .all(|(a, b)| level::is_def_eq(a, b))
                        {
                            return reject(
                                "constructor conclusion applies inductive type at wrong universes",
                            );
                        }
                    }
                    _ => {
                        return reject(
                            "constructor conclusion is not the inductive type being defined",
                        )
                    }
                }
                let t_ni = infos.get(tname).map(|i| i.num_indices).unwrap_or(0);
                if args.len() != (num_params + t_ni) as usize {
                    return reject("constructor conclusion has wrong number of arguments");
                }
                for i in 0..num_params as usize {
                    let expected = expr::bvar((c2.len() as u32) - 1 - i as u32);
                    if !self.is_def_eq(&c2, &args[i], &expected)? {
                        return reject("constructor does not apply the inductive type to its own shared parameters");
                    }
                }
                for idx_arg in &args[num_params as usize..] {
                    if self.occurs_any(idx_arg, &all) {
                        return reject("constructor index expression refers to the inductive type being defined");
                    }
                }
            }
        }
        Ok(())
    }

    /// Walk a constructor's argument telescope; each argument type must be
    /// strictly positive in the names being defined (`bound`).
    fn check_positivity(&self, ctx: &Ctx, e: &Expr, bound: &[u32], _strict_pos_ok: bool) -> R<()> {
        let w = self.whnf(ctx, e).unwrap_or_else(|_| e.clone());
        match &**w {
            ExprData::Pi(_, dom, body) => {
                self.check_arg_positive(ctx, dom, bound, 0)?;
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(dom.clone());
                self.check_positivity(&ctx2, body, bound, _strict_pos_ok)
            }
            _ => Ok(()),
        }
    }

    /// Strict positivity: `bound` may not occur in a Pi domain. Direct
    /// `I params..` is allowed. Nested `F … (I params) …` is allowed when `F`
    /// is a previously defined inductive and `I`'s parameters are uniform.
    fn check_arg_positive(
        &self,
        ctx: &Ctx,
        arg_ty: &Expr,
        bound: &[u32],
        num_params: u32,
    ) -> R<()> {
        let mut cur = self.whnf(ctx, arg_ty).unwrap_or_else(|_| arg_ty.clone());
        let mut ctx2 = {
            crate::stats::ctx_clone();
            ctx.clone()
        };
        loop {
            match &**cur {
                ExprData::Pi(_, dom, body) => {
                    if self.occurs_any(dom, bound) {
                        return reject(
                            "non-positive (negative) occurrence in constructor argument",
                        );
                    }
                    ctx2.push(dom.clone());
                    cur = self.whnf(&ctx2, body).unwrap_or_else(|_| body.clone());
                }
                _ => break,
            }
        }
        self.check_positive_spine(&ctx2, &cur, bound, num_params)
    }

    fn expected_param_args(&self, ctx: &Ctx, num_params: u32) -> Vec<Expr> {
        (0..num_params)
            .map(|i| expr::bvar((ctx.len() as u32).saturating_sub(1 + i)))
            .collect()
    }

    fn check_uniform_i(&self, ctx: &Ctx, args: &[Expr], bound: &[u32], num_params: u32) -> R<()> {
        for a in args {
            if self.occurs_any(a, bound) {
                return reject("nested inductive occurrence in an index");
            }
        }
        if (args.len() as u32) < num_params {
            return reject("nested inductive applied to too few parameters");
        }
        let expected = self.expected_param_args(ctx, num_params);
        for (a, e) in args.iter().zip(expected.iter()) {
            if !self.is_def_eq(ctx, a, e).unwrap_or(false) {
                return reject("non-uniform nested inductive parameter");
            }
        }
        Ok(())
    }

    fn check_positive_spine(&self, ctx: &Ctx, e: &Expr, bound: &[u32], num_params: u32) -> R<()> {
        if !self.occurs_any(e, bound) {
            return Ok(());
        }
        let (h, args) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) if bound.contains(n) => {
                self.check_uniform_i(ctx, &args, bound, num_params)
            }
            ExprData::Const(n, _) => match self.env.get(*n) {
                Some(ConstantInfo::InductiveType { .. }) => {
                    for a in &args {
                        self.check_positive_spine(ctx, a, bound, num_params)?;
                    }
                    Ok(())
                }
                _ => reject("occurrence of inductive type in unsupported position"),
            },
            _ => reject("occurrence of inductive type in unsupported position"),
        }
    }

    fn occurs_any(&self, e: &Expr, names: &[u32]) -> bool {
        match &***e {
            ExprData::Const(n, _) => names.contains(n),
            ExprData::App(f, a) => self.occurs_any(f, names) || self.occurs_any(a, names),
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                self.occurs_any(t, names) || self.occurs_any(b, names)
            }
            ExprData::Let(t, v, b) => {
                self.occurs_any(t, names) || self.occurs_any(v, names) || self.occurs_any(b, names)
            }
            ExprData::Proj(_, _, v) => self.occurs_any(v, names),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level;

    fn ty(n: u32) -> Expr {
        expr::const_(n, vec![])
    }

    fn ctx_of(ns: &[u32]) -> Ctx {
        let mut c = Ctx::new();
        for n in ns {
            c.push(ty(*n));
        }
        c
    }

    /// The inference cache is keyed on this id, so equal ids must mean equal
    /// contexts. Anything weaker turns a cache hit into a type inferred under
    /// the wrong bindings.
    /// `iota_from_first_principles` walks a constructor's fields by peeling
    /// one Pi at a time and instantiating the binder with the field. Because
    /// `instantiate1` discharges that binder, the residual type stays at the
    /// caller's depth — the loop must not also extend the context. It used to,
    /// so the k-th field was processed k binders too deep and the resulting
    /// spine carried indices uniformly off by one.
    #[test]
    fn instantiate1_keeps_the_type_at_the_same_depth() {
        let s0 = expr::sort(level::zero());
        // (Π A. Π B. #1 #0), the shape of a two-field constructor type.
        let inner = expr::pi(
            expr::BinderInfo::Default,
            s0.clone(),
            expr::app(expr::bvar(1), expr::bvar(0)),
        );
        let ct = expr::pi(expr::BinderInfo::Default, s0.clone(), inner);
        let field = expr::const_(7, vec![]);

        let body = match &**ct {
            ExprData::Pi(_, _, b) => b.clone(),
            _ => unreachable!(),
        };
        let next = expr::instantiate1(&body, &field);
        assert_eq!(
            expr::loose_bvar_range(&next),
            expr::loose_bvar_range(&ct),
            "instantiating the peeled binder must not deepen the residual type"
        );
    }

    #[test]
    fn ctx_id_identifies_the_binding_sequence() {
        assert_eq!(Ctx::new().id, 0, "the empty context is the zero id");
        assert_ne!(
            ctx_of(&[1]).id,
            0,
            "a non-empty context is never the zero id"
        );

        // Same types pushed in the same order: same id, however they were built.
        assert_eq!(ctx_of(&[1, 2, 3]).id, ctx_of(&[1, 2, 3]).id);
        let mut grown = ctx_of(&[1, 2]);
        grown.push(ty(3));
        assert_eq!(grown.id, ctx_of(&[1, 2, 3]).id);

        // Order is part of the identity: these bind different types at bvar 0.
        assert_ne!(ctx_of(&[1, 2]).id, ctx_of(&[2, 1]).id);

        // Same length, different types.
        assert_ne!(ctx_of(&[1, 2]).id, ctx_of(&[1, 3]).id);

        // A prefix is a different context from its extension.
        assert_ne!(ctx_of(&[1, 2]).id, ctx_of(&[1, 2, 3]).id);

        // Distinct types really are distinct pushes.
        assert_ne!(ctx_of(&[1]).id, ctx_of(&[2]).id);
    }

    #[test]
    fn ctx_id_tracks_every_push() {
        let mut c = Ctx::new();
        let mut seen = vec![c.id];
        for n in 0..8u32 {
            c.push(ty(n));
            assert_eq!(c.len(), n as usize + 1);
            assert!(
                !seen.contains(&c.id),
                "push must not reuse an ancestor's id"
            );
            seen.push(c.id);
        }
    }

    #[test]
    fn ctx_indexes_from_the_bottom() {
        let c = ctx_of(&[7, 8, 9]);
        assert!(Rc::ptr_eq(&c[0], &ty(7)));
        assert!(Rc::ptr_eq(&c[2], &ty(9)));
        // local_ty reads bvar i as the i-th binder from the top.
        let t0 = local_ty(&c, 0).unwrap();
        assert!(Rc::ptr_eq(&t0, &ty(9)), "bvar 0 is the innermost binder");
        let t2 = local_ty(&c, 2).unwrap();
        assert!(Rc::ptr_eq(&t2, &ty(7)));
        assert!(local_ty(&c, 3).is_none());
    }

    #[test]
    fn ctx_id_is_insensitive_to_cloning() {
        let a = ctx_of(&[1, 2]);
        let b = a.clone();
        assert_eq!(a.id, b.id);
        let mut c = b.clone();
        c.push(expr::sort(level::zero()));
        assert_eq!(
            a.id, b.id,
            "extending a clone must not disturb the original"
        );
        assert_ne!(c.id, a.id);
    }

    /// Shared spine, exponential tree size, intern depth = `depth`.
    fn bush(base: Expr, depth: u32) -> Expr {
        let mut e = base;
        for _ in 0..depth {
            e = expr::app(e.clone(), e.clone());
        }
        e
    }

    /// Eager delta is size/hint, not a library name. A Regular body at the
    /// size cap stays folded; an abbrev still unfolds.
    #[test]
    fn large_regular_def_is_not_eagerly_deltaed() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        let sort0 = expr::sort(level::zero());
        let dummy = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort0.clone(),
                is_unsafe: false,
            },
        );
        let small_body = dummy.clone();
        env.insert(
            1,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: small_body.clone(),
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let large_body = bush(dummy.clone(), 16);
        env.insert(
            2,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: large_body,
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let medium = bush(dummy.clone(), 10);
        env.insert(
            3,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: medium,
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let big = bush(dummy.clone(), 12);
        env.insert(
            4,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: big,
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let names = [
            std::rc::Rc::new("Dummy".into()),
            std::rc::Rc::new("smallAbbrev".into()),
            std::rc::Rc::new("largeRegular".into()),
            std::rc::Rc::new("mediumRegular".into()),
            std::rc::Rc::new("midRegular".into()),
        ];
        let tc = Checker::new(&env, &names, None, None);
        let ctx = Ctx::new();
        assert!(
            tc.delta_body_is_small(1),
            "abbrev is small for same-head delta"
        );
        assert!(
            !tc.delta_body_is_small(2),
            "large Regular is not small for same-head delta"
        );
        let w_small = tc.whnf(&ctx, &expr::const_(1, vec![])).unwrap();
        assert!(
            Rc::ptr_eq(&w_small, &small_body),
            "small/abbrev def still unfolds"
        );
        let w_large = tc.whnf(&ctx, &expr::const_(2, vec![])).unwrap();
        match &**w_large {
            ExprData::Const(n, _) => {
                assert_eq!(*n, 2, "circuit-sized Regular stays folded")
            }
            other => panic!("large Regular was eagerly delta'd: {other:?}"),
        }

        // Multi-arg Prop structure instance: stay folded on circuit Regulars.
        tc.checking_prop_structure.set(true);
        tc.whnf_cache.borrow_mut().clear();
        let w = tc.whnf(&ctx, &expr::const_(4, vec![])).unwrap();
        assert!(
            matches!(&**w, ExprData::Const(4, _)),
            "Prop-structure instance does not instantiate a circuit Regular"
        );
        tc.checking_prop_structure.set(false);
        tc.decl_value_size.set(5_000);
        tc.whnf_cache.borrow_mut().clear();
        let w = tc.whnf(&ctx, &expr::const_(3, vec![])).unwrap();
        assert!(
            !matches!(&**w, ExprData::Const(3, _)),
            "non-structure decl still unfolds a medium Regular"
        );

        // Small decls unfold large Regulars. Huge proofs stay below the
        // circuit ceiling; equation lemmas use `eq_related_defs`.
        tc.decl_value_size.set(5_000);
        tc.whnf_cache.borrow_mut().clear();
        let w = tc.whnf(&ctx, &expr::const_(4, vec![])).unwrap();
        assert!(
            !matches!(&**w, ExprData::Const(4, _)),
            "small decl still unfolds a circuit-sized Regular"
        );
        tc.decl_value_size.set(20_000);
        tc.checking_large_theorem.set(true);
        tc.whnf_cache.borrow_mut().clear();
        let w = tc.whnf(&ctx, &expr::const_(4, vec![])).unwrap();
        assert!(
            matches!(&**w, ExprData::Const(4, _)),
            "huge theorem does not instantiate a circuit Regular"
        );
        tc.checking_large_theorem.set(false);
        tc.eq_related_defs.borrow_mut().push(4);
        tc.whnf_cache.borrow_mut().clear();
        let w = tc.whnf(&ctx, &expr::const_(4, vec![])).unwrap();
        assert!(
            !matches!(&**w, ExprData::Const(4, _)),
            "equality-related Regular still unfolds"
        );
    }

    #[test]
    fn ensure_pi_one_step_unfolds_large_regular() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        let sort0 = expr::sort(level::zero());
        let dummy = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort0.clone(),
                is_unsafe: false,
            },
        );
        let huge_dom = bush(dummy, 16);
        let body = expr::pi(expr::BinderInfo::Default, huge_dom, sort0.clone());
        env.insert(
            1,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::sort(level::succ(level::zero())),
                value: body,
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let names = [
            std::rc::Rc::new("Dummy".into()),
            std::rc::Rc::new("largePiType".into()),
        ];
        let tc = Checker::new(&env, &names, None, None);
        let got = tc.ensure_pi(&Ctx::new(), &expr::const_(1, vec![]));
        assert!(
            got.is_ok(),
            "ensure_pi one-step unfolds a large Regular wrapping a Pi: {got:?}"
        );
    }

    fn regulars_for_name_test() -> crate::env::Environment {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        let sort0 = expr::sort(level::zero());
        let dummy = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort0.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: dummy.clone(),
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: bush(dummy.clone(), 16),
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0.clone(),
                value: bush(dummy.clone(), 12),
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0,
                value: bush(dummy, 14),
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        env
    }

    /// AIG / BVDecide / LawfulOperator / `denote_*` names must not change
    /// eager-delta. Same bodies and hints, different strings.
    #[test]
    fn eager_delta_ignores_library_names() {
        let env = regulars_for_name_test();
        let aig = [
            std::rc::Rc::new("Dummy".into()),
            std::rc::Rc::new("Std.Tactic.BVDecide.LRAT.bitblast.go".into()),
            std::rc::Rc::new("Std.Sat.AIG.Relabel.go._unary".into()),
            std::rc::Rc::new("Std.Sat.AIG.RefVec.denote_eval".into()),
            std::rc::Rc::new("Std.Tactic.BVDecide.Bitblast.instLawfulOperator".into()),
        ];
        let dummy = [
            std::rc::Rc::new("Dummy".into()),
            std::rc::Rc::new("Foo.helper".into()),
            std::rc::Rc::new("Bar.aux._unary".into()),
            std::rc::Rc::new("Baz.lemma".into()),
            std::rc::Rc::new("Qux.instThing".into()),
        ];
        let tc_a = Checker::new(&env, &aig, None, None);
        let tc_b = Checker::new(&env, &dummy, None, None);
        let modes = [
            (0, false, false),
            (200, true, false),
            (200, false, true),
            (5_000, false, false),
            (20_000, false, false),
        ];
        for (size, prop, simple) in modes {
            tc_a.decl_value_size.set(size);
            tc_b.decl_value_size.set(size);
            tc_a.checking_prop_structure.set(prop);
            tc_b.checking_prop_structure.set(prop);
            tc_a.checking_simple_prop_inductive.set(simple);
            tc_b.checking_simple_prop_inductive.set(simple);
            for n in 1..=4u32 {
                assert_eq!(
                    tc_a.eager_whnf_unfolds(n),
                    tc_b.eager_whnf_unfolds(n),
                    "eager_whnf_unfolds({n}) size={size} prop={prop} simple={simple}"
                );
                assert_eq!(
                    tc_a.delta_body_is_small(n),
                    tc_b.delta_body_is_small(n),
                    "delta_body_is_small({n})"
                );
            }
        }
    }

    fn nest_pis(arity: u32, cod: Expr) -> Expr {
        let mut t = cod;
        for _ in 0..arity {
            t = expr::pi(
                expr::BinderInfo::Default,
                expr::sort(level::succ(level::zero())),
                t,
            );
        }
        t
    }

    /// Class / Eq / 1-field Prop shapes are inductive metadata, not names.
    #[test]
    fn inductive_shapes_ignore_library_names() {
        use crate::env::{ConstantInfo, Environment};
        let sort0 = expr::sort(level::zero());
        let mut env = Environment::default();
        env.insert(
            0,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: nest_pis(5, sort0.clone()),
                num_params: 5,
                num_indices: 0,
                all: vec![0],
                ctors: vec![1],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: sort0.clone(),
                induct: 0,
                cidx: 0,
                num_params: 5,
                num_fields: 2,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: nest_pis(3, sort0.clone()),
                num_params: 1,
                num_indices: 2,
                all: vec![2],
                ctors: vec![3],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: sort0.clone(),
                induct: 2,
                cidx: 0,
                num_params: 1,
                num_fields: 1,
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: nest_pis(1, sort0.clone()),
                num_params: 1,
                num_indices: 0,
                all: vec![4],
                ctors: vec![5],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            5,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: sort0,
                induct: 4,
                cidx: 0,
                num_params: 1,
                num_fields: 1,
                is_unsafe: false,
            },
        );
        let lib = [
            std::rc::Rc::new("LawfulVecOperator".into()),
            std::rc::Rc::new("LawfulVecOperator.mk".into()),
            std::rc::Rc::new("Eq".into()),
            std::rc::Rc::new("Eq.refl".into()),
            std::rc::Rc::new("Finite".into()),
            std::rc::Rc::new("Finite.mk".into()),
        ];
        let dummy = [
            std::rc::Rc::new("MyClass".into()),
            std::rc::Rc::new("MyClass.mk".into()),
            std::rc::Rc::new("MyEq".into()),
            std::rc::Rc::new("MyEq.refl".into()),
            std::rc::Rc::new("MyFin".into()),
            std::rc::Rc::new("MyFin.mk".into()),
        ];
        let tc_a = Checker::new(&env, &lib, None, None);
        let tc_b = Checker::new(&env, &dummy, None, None);
        let class_ty = expr::const_(0, vec![]);
        let eq_ty = expr::const_(2, vec![]);
        let fin_ty = expr::const_(4, vec![]);
        assert!(tc_a.type_is_multiarg_prop_structure(&class_ty));
        assert!(!tc_a.type_is_multiarg_prop_structure(&eq_ty));
        assert!(!tc_a.type_is_multiarg_prop_structure(&fin_ty));
        assert!(tc_a.type_is_equality_shaped(&eq_ty));
        assert!(!tc_a.type_is_equality_shaped(&class_ty));
        assert!(!tc_a.type_is_equality_shaped(&fin_ty));
        assert_eq!(
            tc_a.type_is_equality_shaped(&eq_ty),
            tc_b.type_is_equality_shaped(&eq_ty)
        );
        assert!(tc_a.type_is_unit_ctor_zero_index_prop(&class_ty));
        assert!(!tc_a.type_is_unit_ctor_zero_index_prop(&eq_ty));
        assert!(tc_a.type_is_unit_ctor_zero_index_prop(&fin_ty));
        assert_eq!(
            tc_a.type_is_multiarg_prop_structure(&class_ty),
            tc_b.type_is_multiarg_prop_structure(&class_ty)
        );
        assert_eq!(
            tc_a.type_is_unit_ctor_zero_index_prop(&fin_ty),
            tc_b.type_is_unit_ctor_zero_index_prop(&fin_ty)
        );
        let mut rel_a = Vec::new();
        let mut rel_b = Vec::new();
        tc_a.fill_eq_related_defs(&eq_ty, &mut rel_a);
        tc_b.fill_eq_related_defs(&eq_ty, &mut rel_b);
        assert_eq!(rel_a, rel_b);
        let mut rel_class = Vec::new();
        tc_a.fill_eq_related_defs(&class_ty, &mut rel_class);
        assert!(
            rel_class.is_empty(),
            "class-like Prop is not equality-shaped"
        );
    }
}
