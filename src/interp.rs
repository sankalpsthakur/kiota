//! Library interpreters gated to exact interned env names.
//!
//! Lean's kernel has no grind/omega/Rat evaluator. Reduction fires only when
//! the head constant's interned name equals `Int.Linear.*` / `Lean.Grind.*` /
//! `Lean.Omega.*` / `Rat.*` / `dite` / `ite` / `Int.decLe` (full name, not a
//! substring).

use crate::expr::{self, Expr, ExprData, Lit};
use crate::level;
use crate::nat;
use crate::tc::{Checker, Ctx, R};
use num_bigint::{BigInt, BigUint, Sign};

fn exact_qual(name: &str, prefix: &str, ident: &str) -> bool {
    name.strip_prefix(prefix) == Some(ident)
}

fn is_int_linear_head(name: &str) -> bool {
    name == "Int.Linear" || name.starts_with("Int.Linear.")
}

fn is_commring_head(name: &str) -> bool {
    name == "Lean.Grind.CommRing" || name.starts_with("Lean.Grind.CommRing.")
}

fn is_rarray_head(name: &str) -> bool {
    name == "Lean.RArray" || name.starts_with("Lean.RArray.")
}

/// Lean `Int.pow m n`: `|m|^n` with sign `sign(m)^n`. `n = 0` yields `1`.
pub(crate) fn int_pow(base: &BigInt, exp: &BigUint) -> Option<BigInt> {
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
pub(crate) fn int_emod_nat(a: &BigInt, m: &BigUint) -> BigInt {
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
pub(crate) fn int_bmod(x: &BigInt, m: &BigUint) -> BigInt {
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
pub(crate) fn int_ediv(a: &BigInt, b: &BigInt) -> BigInt {
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
pub(crate) fn int_cdiv(a: &BigInt, b: &BigInt) -> BigInt {
    -int_ediv(&-a, b)
}

/// Lean `Int.Linear.cmod a b` = `-((-a) % b)`.
pub(crate) fn int_cmod(a: &BigInt, b: &BigInt) -> BigInt {
    -int_emod(&-a, b)
}

fn is_int_linear_ident(name: &str, ident: &str) -> bool {
    exact_qual(name, "Int.Linear.", ident)
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
    exact_qual(name, "Lean.Grind.CommRing.", ident)
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

pub(crate) fn num_bigint_gcd(a: &BigUint, b: &BigUint) -> BigUint {
    let mut x = a.clone();
    let mut y = b.clone();
    while y != BigUint::from(0u32) {
        let r = &x % &y;
        x = y;
        y = r;
    }
    x
}

impl<'e> Checker<'e> {
    fn find_lib(&self, suffix: &str) -> Option<u32> {
        let mapped = match suffix {
            "Int" => "Int",
            "Int.ofNat" => "Int.ofNat",
            "Int.negSucc" => "Int.negSucc",
            "Int.neg" => "Int.neg",
            "Int.add" => "Int.add",
            "Int.sub" => "Int.sub",
            "Int.mul" => "Int.mul",
            "Int.pow" => "Int.pow",
            "Nat.add" => "Nat.add",
            "Nat.mul" => "Nat.mul",
            "Nat.pow" => "Nat.pow",
            "Nat.sub" => "Nat.sub",
            "Nat.mod" => "Nat.mod",
            "Nat.div" => "Nat.div",
            "Nat.shiftLeft" => "Nat.shiftLeft",
            "Nat.shiftRight" => "Nat.shiftRight",
            "HAdd.hAdd" => "HAdd.hAdd",
            "HSub.hSub" => "HSub.hSub",
            "LinearCombo.add" => "Lean.Omega.LinearCombo.add",
            "LinearCombo.sub" => "Lean.Omega.LinearCombo.sub",
            "LinearCombo.mk" => "Lean.Omega.LinearCombo.mk",
            "LinearCombo" => "Lean.Omega.LinearCombo",
            "Constraint.mk" => "Lean.Omega.Constraint.mk",
            "Coeffs.dot" => "Lean.Omega.Coeffs.dot",
            "Coeffs.sub" => "Lean.Omega.Coeffs.sub",
            "Coeffs.add" => "Lean.Omega.Coeffs.add",
            "IntList.sub" => "Lean.Omega.IntList.sub",
            "IntList.add" => "Lean.Omega.IntList.add",
            "instOfNatInt" => "instOfNatInt",
            "instNegInt" => "Int.instNegInt",
            other => other,
        };
        self.find_name(mapped).or_else(|| match suffix {
            "instOfNatInt" => self.find_name("Int.instOfNatInt"),
            "instNegInt" => self.find_name("instNegInt"),
            _ => None,
        })
    }

    pub(crate) fn try_hbin_nat(&self, ctx: &Ctx, name: &str, args: &[Expr]) -> R<Option<Expr>> {
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
        let is_combo = ty_name == "Lean.Omega.LinearCombo";
        let is_int_name = |s: &str| s == "Int";
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
        let Some(opn) = self.find_lib(op) else {
            return Ok(None);
        };
        let lhs = args[lhs_i].clone();
        let rhs = args[lhs_i + 1].clone();
        let r = expr::apps(expr::const_(opn, vec![]), &[lhs, rhs]);
        Ok(Some(expr::apps(r, &args[need..])))
    }

    /// `dite α c (isTrue p h) t e → t h` and `isFalse` → `e h`.
    /// `ite` drops the proof. Fires in `whnf_core` so height-based delta
    /// cannot unfold `modCore.go` before the instance constructor is seen.
    /// Closed `Rat` projections / `inv`. `Rat.zpow_neg`'s `with_unfolding_all
    /// rfl` needs `1⁻¹ = 1`; `Rat.inv` is a `dite` on `a.num < 0` whose
    /// `Decidable` stays stuck unless `.num`/`.den` of `OfNat Rat n` reduce.
    pub(crate) fn try_rat(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let is_inv = name == "Rat.inv";
        let is_num = name == "Rat.num";
        let is_den = name == "Rat.den";
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
                s == "Rat"
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
        if name == "Rat.mk'" && args.len() >= 4 {
            let Some(num) = self.closed_int_value(ctx, &args[args.len() - 4])? else {
                return Ok(None);
            };
            let Some(den) = self.closed_nat_value(ctx, &args[args.len() - 3])? else {
                return Ok(None);
            };
            return Ok(Some((num, den, e)));
        }
        if name == "Rat.ofInt" && !args.is_empty() {
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
        if (name == "NatCast.natCast" || name == "Rat.natCast")
            && args.len() >= 2
            && self.is_rat_const(&args[0])
        {
            let Some(n) = self.closed_nat_value(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some((BigInt::from(n), BigUint::from(1u32), e)));
        }
        if (name == "IntCast.intCast" || name == "Rat.intCast")
            && args.len() >= 2
            && self.is_rat_const(&args[0])
        {
            let Some(n) = self.closed_int_value(ctx, args.last().unwrap())? else {
                return Ok(None);
            };
            return Ok(Some((n, BigUint::from(1u32), e)));
        }
        Ok(None)
    }

    pub(crate) fn try_dite(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
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
        let is_true = iname == "Decidable.isTrue";
        let is_false = iname == "Decidable.isFalse";
        if !is_true && !is_false {
            if is_ite && (iname == "Int.decLe" || iname == "Int.decLt") && iargs.len() >= 2 {
                let aw = self.whnf(ctx, &iargs[0])?;
                let bw = self.whnf(ctx, &iargs[1])?;
                let (Some(a), Some(b)) = (
                    self.closed_int_value(ctx, &aw)?,
                    self.closed_int_value(ctx, &bw)?,
                ) else {
                    return Ok(None);
                };
                let yes = if iname == "Int.decLt" { a < b } else { a <= b };
                let branch = if yes { &args[3] } else { &args[4] };
                return Ok(Some(expr::apps(branch.clone(), &args[5..])));
            }
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
                s == "List.nil"
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
        if s != "List.cons" {
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
            if let Some(int_ty) = self.find_lib("Int") {
                if let Some(inst) = self
                    .find_name("instOfNat")
                    .or_else(|| self.find_lib("instOfNatInt"))
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
    pub(crate) fn try_int_linear(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        let ident = name.rsplit('.').next().unwrap_or(name);
        if !(is_int_linear_head(name)
            || is_rarray_head(name)
            || name == "getElem"
            || name == "GetElem.getElem")
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

        if ident == "get" && is_rarray_head(name) && args.len() >= 2 {
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
        if name == "Int.Linear.Var.denote" && args.len() >= 2 {
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
        if name == "Int.Linear.Expr.denote" && args.len() >= 2 {
            let rctx = &args[args.len() - 2];
            let e = args.last().unwrap();
            if let Some(r) = self.linear_expr_denote(ctx, rctx, e)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if name == "Int.Linear.Poly.denote'" && args.len() >= 2 {
            let rctx = &args[args.len() - 2];
            let p = args.last().unwrap();
            if let Some(r) = self.linear_poly_denote_prime(ctx, rctx, p)? {
                return Ok(Some(expr::apps(r, &args[args.len()..])));
            }
        }
        if name == "Int.Linear.Poly.denote'.go" && args.len() >= 3 {
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
        if ident == "combine" && args.len() >= 2 && name == "Int.Linear.Poly.combine" {
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
        let n = self.find_lib(op)?;
        Some(expr::apps(expr::const_(n, vec![]), &[a, b]))
    }

    fn mk_int_un(&self, op: &str, a: Expr) -> Option<Expr> {
        let n = self.find_lib(op)?;
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
        let int = self.find_lib("Int")?;
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
        let int = self.find_lib("Int")?;
        let inst = self
            .find_name("Int.instNegInt")
            .or_else(|| self.find_lib("instNegInt"))?;
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
            if name == "Lean.RArray.leaf" && !args.is_empty() {
                return Ok(Some(args.last().unwrap().clone()));
            }
            if name == "Lean.RArray.branch" && args.len() >= 3 {
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
        self.find_name(&format!("Int.Linear.{ident}"))
    }

    fn mk_bool_const(&self, v: bool) -> Option<Expr> {
        let tname = if v { "Bool.true" } else { "Bool.false" };
        let bn = self.find_name(tname)?;
        Some(expr::const_(bn, vec![]))
    }

    /// Closed `Lean.Grind.CommRing` certificates. `toPoly_k` / `combine_k`
    /// are `Expr.rec` / `Nat.rec hugeFuel`; peeling them dies at Init
    /// `#17755` (`norm_cnstr_cert`). Do not intercept `Poly.beq'`.
    pub(crate) fn try_comm_ring(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !is_commring_head(name) {
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
            "norm_eq_cert" if args.len() >= 4 => {
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

    pub(crate) fn try_intlist(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !(name.starts_with("Lean.Omega.IntList.")
            || name.starts_with("Lean.Omega.Coeffs.")
            || name == "Lean.Omega.IntList"
            || name == "Lean.Omega.Coeffs")
        {
            return Ok(None);
        }
        let ends = |s: &str| name == format!("Lean.Omega.{s}") || name == s;
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
        if name == "Option.none" {
            return Some(None);
        }
        if name == "Option.some" {
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
        if name == "Lean.Omega.Constraint.mk" && args.len() >= 2 {
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
    pub(crate) fn try_omega_constraint(
        &self,
        ctx: &Ctx,
        head: &Expr,
        args: &[Expr],
    ) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if name == "Lean.Omega.tidyConstraint" || name == "Lean.Omega.tidyCoeffs" {
            if args.len() >= 2 {
                if let Some((c, xs)) = self.omega_tidy(ctx, &args[0], &args[1])? {
                    let r = if name == "Lean.Omega.tidyConstraint" {
                        c
                    } else {
                        xs
                    };
                    return Ok(Some(expr::apps(r, &args[2..])));
                }
            }
            return Ok(None);
        }
        if !name.starts_with("Lean.Omega.Constraint.") && name != "Lean.Omega.Constraint" {
            return Ok(None);
        }
        let ends = |s: &str| name == format!("Lean.Omega.{s}") || name == s;
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
            let Some(mk) = self.find_lib("Constraint.mk") else {
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
        let Some(mk) = self.find_lib("Constraint.mk") else {
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
        let int_ty = expr::const_(self.find_lib("Int")?, vec![]);
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
        let Some(mk) = self.find_lib("Constraint.mk") else {
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
    pub(crate) fn is_closed_int_numeral(&self, e: &Expr) -> bool {
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
        if name == "Int.ofNat" {
            return !args.is_empty() && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.negSucc" {
            return !args.is_empty() && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.neg" || name == "Neg.neg" {
            return args.last().is_some_and(|a| self.is_closed_int_numeral(a));
        }
        false
    }

    /// `Int.neg x` or `Neg.neg Int _ x` → `x`. Used only to cancel a
    /// second closed negation (`- - n = n`); open `n` must stay a `neg`
    /// so `Int.neg_neg` still matches its recursor motive.
    pub(crate) fn peel_int_neg(&self, e: &Expr) -> Option<Expr> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if name == "Int.neg" {
            return args.first().cloned();
        }
        if name == "Neg.neg" && args.len() >= 3 {
            return Some(args[2].clone());
        }
        None
    }

    pub(crate) fn closed_nat_value(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigUint>> {
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
    fn type_head_is_int(&self, e: &Expr) -> bool {
        let (h, _) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) => self.name_str(*n) == "Int",
            _ => false,
        }
    }

    pub(crate) fn closed_int_value(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigInt>> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        if name == "OfNat.ofNat" && args.len() >= 2 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let Some(n) = self.closed_nat_value(ctx, &args[1])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if name == "Int.ofNat" {
            if let Some(n) = args.first() {
                if let Some(v) = self.closed_nat_value(ctx, n)? {
                    return Ok(Some(BigInt::from(v)));
                }
            }
            return Ok(None);
        }
        if name == "Int.negSucc" {
            if let Some(n) = args.first() {
                if let Some(v) = self.closed_nat_value(ctx, n)? {
                    return Ok(Some(-BigInt::from(v) - 1));
                }
            }
            return Ok(None);
        }
        if name == "Int.neg" {
            if let Some(a) = args.first() {
                if let Some(v) = self.closed_int_value(ctx, a)? {
                    return Ok(Some(-v));
                }
            }
            return Ok(None);
        }
        if name == "Neg.neg" && args.len() >= 3 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let Some(v) = self.closed_int_value(ctx, &args[2])? {
                return Ok(Some(-v));
            }
            return Ok(None);
        }
        if (name == "Int.ediv" || name == "Int.div") && args.len() >= 2 {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_int_value(ctx, &args[1])?,
            ) {
                return Ok(Some(int_ediv(&a, &b)));
            }
            return Ok(None);
        }
        if name == "HDiv.hDiv" && args.len() >= 6 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[4])?,
                self.closed_int_value(ctx, &args[5])?,
            ) {
                return Ok(Some(int_ediv(&a, &b)));
            }
            return Ok(None);
        }
        if (name == "Nat.cast" || name == "NatCast.natCast") && args.len() >= 3 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let Some(n) = self.closed_nat_value(ctx, &args[2])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if name == "NatCast.natCast" && args.len() >= 2 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let Some(n) = self.closed_nat_value(ctx, &args[1])? {
                return Ok(Some(BigInt::from(n)));
            }
            return Ok(None);
        }
        if (name == "Int.pow") && args.len() >= 2 {
            if let (Some(a), Some(e)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_nat_value(ctx, &args[1])?,
            ) {
                return Ok(int_pow(&a, &e));
            }
            return Ok(None);
        }
        if name == "HPow.hPow" && args.len() >= 6 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
            if let (Some(a), Some(e)) = (
                self.closed_int_value(ctx, &args[4])?,
                self.closed_nat_value(ctx, &args[5])?,
            ) {
                return Ok(int_pow(&a, &e));
            }
            return Ok(None);
        }
        if (name == "Int.bmod") && args.len() >= 2 {
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
        if (name == "Int.add" || name == "Int.sub" || name == "Int.mul") && args.len() >= 2 {
            if let (Some(a), Some(b)) = (
                self.closed_int_value(ctx, &args[0])?,
                self.closed_int_value(ctx, &args[1])?,
            ) {
                return Ok(Some(if name == "Int.add" {
                    a + b
                } else if name == "Int.sub" {
                    a - b
                } else {
                    a * b
                }));
            }
            return Ok(None);
        }
        if (name == "HAdd.hAdd" || name == "HSub.hSub" || name == "HMul.hMul") && args.len() >= 6 {
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
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
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
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
    pub(crate) fn mk_int_canonical(&self, v: &BigInt) -> Option<Expr> {
        if v.sign() != Sign::Minus {
            let ofn = self.find_lib("Int.ofNat")?;
            return Some(expr::app(
                expr::const_(ofn, vec![]),
                nat::mk_lit(v.magnitude().clone()),
            ));
        }
        let ns = self.find_lib("Int.negSucc")?;
        let mag = v.magnitude();
        if *mag == BigUint::from(0u32) {
            return None;
        }
        Some(expr::app(expr::const_(ns, vec![]), nat::mk_lit(mag - 1u32)))
    }

    pub(crate) fn mk_closed_int(&self, v: &BigInt) -> Option<Expr> {
        if v.sign() == Sign::Minus {
            let pos = self.mk_closed_int(&-v)?;
            let ineg = self.find_lib("Int.neg")?;
            return Some(expr::app(expr::const_(ineg, vec![]), pos));
        }
        let n: BigUint = v.magnitude().clone();
        let ofnat = self.find_name("OfNat.ofNat")?;
        let int_ty = self.find_lib("Int")?;
        let inst = self
            .find_name("instOfNat")
            .or_else(|| self.find_lib("instOfNatInt"))?;
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
        if (name == "Int.ofNat") && !args.is_empty() {
            if let ExprData::Lit(Lit::Nat(n)) = &**args[0] {
                return *n == num_bigint::BigUint::from(0u32);
            }
        }
        false
    }

    fn linear_combo_mk_parts(&self, e: &Expr) -> Option<(Expr, Expr)> {
        let (h, args) = expr::unfold_apps(e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return None,
        };
        if name == "Lean.Omega.LinearCombo.mk" && args.len() >= 2 {
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
            if (name == "Lean.Omega.Coeffs.ofList" || name == "Lean.Omega.IntList.ofList")
                && !args.is_empty()
            {
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
        let int_ty = self.find_lib("Int")?;
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
        let Some(mk) = self.find_lib("LinearCombo.mk") else {
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
    pub(crate) fn try_omega_combo(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let n = match &***head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let name = self.name_str(n);
        if !name.starts_with("Lean.Omega.LinearCombo.") && name != "Lean.Omega.LinearCombo" {
            return Ok(None);
        }
        let ends = |s: &str| name == format!("Lean.Omega.{s}") || name == s;
        let Some(combo) = self.find_lib("LinearCombo") else {
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
            let (cnst, coeffs) = if lname == "Lean.Omega.LinearCombo.mk" && largs.len() >= 2 {
                (largs[0].clone(), largs[1].clone())
            } else {
                (expr::proj(combo, 0, lc.clone()), expr::proj(combo, 1, lc))
            };
            let coeffs_w = self.whnf(ctx, &coeffs)?;
            if self.is_list_nil(&coeffs_w) {
                return Ok(Some(expr::apps(cnst, &args[2..])));
            }
            let dot = self.find_lib("Coeffs.dot");
            let iadd = self.find_lib("Int.add");
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
            let Some(mk) = self.find_lib("LinearCombo.mk") else {
                return Ok(None);
            };
            let ac = expr::proj(combo, 0, a.clone());
            let bc = expr::proj(combo, 0, b.clone());
            let aco = expr::proj(combo, 1, a);
            let bco = expr::proj(combo, 1, b);
            let (const_, coeffs) = if ends("LinearCombo.sub") {
                let Some(isub) = self.find_lib("Int.sub") else {
                    return Ok(None);
                };
                let csub = self
                    .find_lib("Coeffs.sub")
                    .or_else(|| self.find_lib("IntList.sub"));
                let coeffs = if let Some(csub) = csub {
                    expr::apps(expr::const_(csub, vec![]), &[aco, bco])
                } else if let Some(hsub) = self.find_lib("HSub.hSub") {
                    expr::apps(expr::const_(hsub, vec![]), &[aco, bco])
                } else {
                    return Ok(None);
                };
                (expr::apps(expr::const_(isub, vec![]), &[ac, bc]), coeffs)
            } else {
                let Some(iadd) = self.find_lib("Int.add") else {
                    return Ok(None);
                };
                let cadd = self
                    .find_lib("Coeffs.add")
                    .or_else(|| self.find_lib("IntList.add"));
                let coeffs = if let Some(cadd) = cadd {
                    expr::apps(expr::const_(cadd, vec![]), &[aco, bco])
                } else if let Some(hadd) = self.find_lib("HAdd.hAdd") {
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
}
