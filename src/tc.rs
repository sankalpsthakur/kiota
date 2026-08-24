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
    /// `whnf_core` → iota → `whnf_major` → `whnf_core` is not counted by
    /// `WHNF_DEPTH` (that only wraps the outer `whnf` entry). Unbounded it
    /// overflows the 1GB worker stack (`BitVec.msb_eq_decide`).
    static CORE_DEPTH: Cell<u32> = const { Cell::new(0) };
    /// Set when `whnf_core` hits CONV_DEPTH. The abort is a Decline, never a
    /// stuck term cached or returned as WHNF (criterion 2).
    static CORE_ABORTED: Cell<bool> = const { Cell::new(false) };
    /// Unreduced same-const App congruence (`try_unreduced` + `is_def_eq_core`
    /// pairwise) nested 15+ deep on class spines walks the *tree*, not the
    /// intern DAG — 7^15 at std `#18000` (`LawfulVecOperator.mk`). One level
    /// keeps Acc.rec unreduced majors; nested Apps WHNF then delta.
    static APP_CONG_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Recursion guard for `whnf` / `is_def_eq`, not a completeness fingerprint.
/// Lean has no 2048 cap; `WellFounded.Nat.fix` / UTF-8 decode proofs nest
/// `Nat.rec` conversion past that (Init `utf8DecodeChar?.assemble₃._proof_3`).
/// Kept well under typical C-stack (~8MB) so this is a decline, not a segfault.
const CONV_DEPTH: u32 = 131_072;

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
    if let Some(rest) = name.strip_suffix(ident) {
        rest == "Int.Linear." || rest.ends_with(".Int.Linear.")
    } else {
        false
    }
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
            LinearPoly::Add(a, v, p) => {
                LinearPoly::Add(k * a, v.clone(), Box::new(p.mul_nz(k)))
            }
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
            (LinearPoly::Num(_), LinearPoly::Add(a2, x2, p2t)) => LinearPoly::Add(
                b * a2,
                x2.clone(),
                Box::new(Self::merge(a, b, p1, p2t)),
            ),
            (LinearPoly::Add(a1, x1, p1t), LinearPoly::Num(_)) => LinearPoly::Add(
                a * a1,
                x1.clone(),
                Box::new(Self::merge(a, b, p1t, p2)),
            ),
            (LinearPoly::Add(a1, x1, p1t), LinearPoly::Add(a2, x2, p2t)) => {
                if x1 == x2 {
                    let c = a * a1 + b * a2;
                    if c.sign() == Sign::NoSign {
                        Self::merge(a, b, p1t, p2t)
                    } else {
                        LinearPoly::Add(c, x1.clone(), Box::new(Self::merge(a, b, p1t, p2t)))
                    }
                } else if x2 < x1 {
                    LinearPoly::Add(
                        a * a1,
                        x1.clone(),
                        Box::new(Self::merge(a, b, p1t, p2)),
                    )
                } else {
                    LinearPoly::Add(
                        b * a2,
                        x2.clone(),
                        Box::new(Self::merge(a, b, p1, p2t)),
                    )
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
            LinearPoly::Add(a, _, p) => {
                int_emod(a, k).sign() == Sign::NoSign && p.div_coeffs(k)
            }
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
    if name == ident {
        return true;
    }
    if let Some(rest) = name.strip_suffix(ident) {
        rest == "Lean.Grind.CommRing." || rest.ends_with(".Lean.Grind.CommRing.")
    } else {
        false
    }
}

fn is_rat_ident(name: &str, ident: &str) -> bool {
    if let Some(rest) = name.strip_suffix(ident) {
        rest == "Rat." || rest.ends_with(".Rat.")
    } else {
        false
    }
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
        CrMon::Mult(CrPower { x, k: BigUint::from(1u32) }, Box::new(CrMon::Unit))
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
                    CrPoly::Add(
                        k * c,
                        m.clone(),
                        Box::new(CrPoly::Num(BigInt::from(0))),
                    )
                }
            }
            CrPoly::Add(c, m2, p) => CrPoly::Add(
                k * c,
                m.mul(m2),
                Box::new(p.mul_mon(k, m)),
            ),
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
                    CrExpr::Num(n) | CrExpr::IntCast(n) => {
                        Some(CrPoly::Num(int_pow(n, k)?))
                    }
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
        assert_eq!(int_ediv(&BigInt::from(-12), &BigInt::from(7)), BigInt::from(-2));
        assert_eq!(int_ediv(&BigInt::from(12), &BigInt::from(-7)), BigInt::from(-1));
        assert_eq!(int_ediv(&BigInt::from(12), &BigInt::from(0)), BigInt::from(0));
    }

    #[test]
    fn pow_matches_lean_int_pow() {
        assert_eq!(int_pow(&BigInt::from(2), &BigUint::from(63u32)).unwrap(), BigInt::from(1u64) << 63);
        assert_eq!(int_pow(&BigInt::from(-2), &BigUint::from(3u32)).unwrap(), BigInt::from(-8));
        assert_eq!(int_pow(&BigInt::from(-2), &BigUint::from(4u32)).unwrap(), BigInt::from(16));
        assert_eq!(int_pow(&BigInt::from(5), &BigUint::from(0u32)).unwrap(), BigInt::from(1));
    }

    #[test]
    fn bmod_two_pow_31_is_min_int32() {
        let p31 = BigInt::from(1u64) << 31;
        let p32 = BigUint::from(1u64) << 32;
        assert_eq!(int_bmod(&p31, &p32), -p31);
        assert_eq!(int_emod_nat(&BigInt::from(-5), &BigUint::from(3u32)), BigInt::from(1));
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
        let b = CrExpr::Sub(Box::new(rhs2), Box::new(lhs2)).to_poly().unwrap();
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

fn decline_or_false(e: TcError) -> R<bool> {
    match e {
        TcError::Decline(msg) => Err(TcError::Decline(msg)),
        _ => Ok(false),
    }
}

pub struct Checker<'e> {
    pub env: &'e Environment,
    pub names: &'e [std::rc::Rc<String>],
    pub nat_ref: Option<u32>,
    pub string_ref: Option<u32>,
    /// `(ctx_key, ptr) → WHNF`. `ctx_key` is 0 for closed terms, `ctx.id` for open.
    whnf_cache: RefCell<FxHashMap<(u64, usize), Expr>>,
    whnf_core_cache: RefCell<FxHashMap<(u64, usize), Expr>>,
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
    /// `(ctx, term) → (type, checked)`. InferOnly may read a Check entry;
    /// Check must not use an InferOnly entry (that skipped app-arg checks).
    infer_cache: RefCell<FxHashMap<(u64, usize), (Expr, bool)>>,
    /// Consts whose telescope has a Prop-inductive binder (`USquash`, `Eq`).
    /// Only those spines need `defeq_args`; everything else stays pairwise.
    proof_arg_cache: RefCell<FxHashMap<u32, bool>>,
    /// Consecutive `Nat.rec` peels of one `bits() >= 20` literal countdown.
    fuel_nat_peels: std::cell::Cell<u32>,
    /// Last bits≥20 literal peeled; used to detect one hugeFuel countdown.
    fuel_nat_last: std::cell::RefCell<Option<num_bigint::BigUint>>,
    /// Lean `infer_only`: skip app-arg checks. Only for PI
    /// (`proofs_of_same_prop`) on already-checked terms.
    infer_only: std::cell::Cell<bool>,
    /// Tree size of the decl value currently being checked (0 = none).
    /// Eager Regular unfold is budgeted against this, not a library name.
    decl_value_size: std::cell::Cell<u32>,
    /// Theorem type is a 1-ctor 0-index Prop inductive with ≥5 params and
    /// ≥2 ctor fields (`LawfulVecOperator` shape, not `Eq`/`And`/`Finite`).
    checking_prop_structure: std::cell::Cell<bool>,
    /// Largest Def body appearing as a head on an equality-shaped type
    /// (`Eq`/`HEq`: 1 ctor, indices > 0, Prop). Small `.eq_1` lemmas of a
    /// 40k Regular need that Regular to unfold; the name is not tested.
    eq_side_def_size: std::cell::Cell<u32>,
    /// Theorem type is a 1-ctor 0-index Prop that is *not* the multi-arg
    /// class (`Finite`, not `LawfulVecOperator`). Those instances need a
    /// higher Regular cap than circuit `_proof_*` lemmas of similar size.
    checking_simple_prop_inductive: std::cell::Cell<bool>,
    /// Defs on an equality-shaped type (and one nested Def mentioned in
    /// those bodies). Unfolded regardless of the size cap so small eq
    /// lemmas of a 3k aux def still reduce.
    eq_related_defs: RefCell<Vec<u32>>,
    /// Eq/HEq argument heads only (not nested / value-scan). `f.eq_def`
    /// must unfold `f` even when `f` is circuit-like.
    eq_arg_heads: RefCell<Vec<u32>>,
}

thread_local! {
    /// Maps `(parent id, pushed type)` to the id of the extended context, so
    /// that two contexts built from the same sequence of types share an id.
    static CTX_IDS: RefCell<FxHashMap<(u64, usize), u64>> = RefCell::new(FxHashMap::default());
    static CTX_NEXT: std::cell::Cell<u64> = const { std::cell::Cell::new(1) };
}

/// Intern `(parent_id, type ptr)` to a context id. Shared by full `ctx.id`
/// and by suffix keys (the k innermost binders of an open term).
fn intern_ctx_id(parent: u64, ty_ptr: usize) -> u64 {
    CTX_IDS.with(|m| {
        *m.borrow_mut().entry((parent, ty_ptr)).or_insert_with(|| {
            CTX_NEXT.with(|c| {
                let v = c.get();
                c.set(v + 1);
                v
            })
        })
    })
}

/// `ctx[len-1-i]` is the raw (unshifted) type recorded for bvar `i`.
///
/// The `id` is what makes a type-inference cache possible. Keying on depth
/// alone would be unsound — two contexts of equal length bind different types
/// — so each context carries an identity interned from the sequence of types
/// that built it. Equal ids therefore imply equal contexts; distinct ids for
/// equal contexts would only cost a cache miss, and interning rules that out.
///
/// `suffix[k]` is the interned id of the **k innermost** binder types
/// (`suffix[0] = 0`). A term with `loose = k` only reads those k binders,
/// so infer/defeq can key on `suffix[k]` instead of the full telescope.
#[derive(Clone)]
struct Ctx {
    /// Invariant: only ever extended through `push`, which keeps `id` in step.
    /// Mutating this directly would leave `id` describing a different context
    /// than `tys` holds, and the inference cache would then hand back a type
    /// inferred under other bindings — a false accept, silently.
    tys: Vec<Expr>,
    id: u64,
    suffix: Vec<u64>,
}

impl Default for Ctx {
    fn default() -> Self {
        Ctx {
            tys: Vec::new(),
            id: 0,
            suffix: vec![0],
        }
    }
}

impl Ctx {
    fn new() -> Self {
        Ctx::default()
    }

    fn push(&mut self, ty: Expr) {
        let ty_ptr = Rc::as_ptr(&ty) as usize;
        let new_id = intern_ctx_id(self.id, ty_ptr);
        let mut suffix = vec![0];
        suffix.push(intern_ctx_id(0, ty_ptr));
        for k in 1..self.tys.len() {
            suffix.push(intern_ctx_id(self.suffix[k], ty_ptr));
        }
        if !self.tys.is_empty() {
            suffix.push(new_id);
        }
        self.id = new_id;
        self.suffix = suffix;
        self.tys.push(ty);
    }

    /// Infer/defeq cache key: closed → 0; otherwise the intern of the types
    /// of **bvars the term actually uses**, not a contiguous suffix of length
    /// `loose`. Extra innermost binders (`Decidable.rec` in `#18041`) must not
    /// split AIG `BinaryInput.mk` pair cache. `used_bvars == u64::MAX` (some
    /// index `≥ 64`) falls back to `suffix[loose]`. Types are stored
    /// unshifted; `local_ty` shifts on read.
    fn term_ctx_key(&self, e: &Expr) -> u64 {
        self.used_bvar_key(expr::used_bvars(e), expr::loose_bvar_range(e))
    }

    fn pair_ctx_key(&self, a: &Expr, b: &Expr) -> u64 {
        let used = expr::used_bvars(a) | expr::used_bvars(b);
        let overflow = expr::used_bvars(a) == u64::MAX || expr::used_bvars(b) == u64::MAX;
        let used = if overflow { u64::MAX } else { used };
        let loose = expr::loose_bvar_range(a).max(expr::loose_bvar_range(b));
        self.used_bvar_key(used, loose)
    }

    fn used_bvar_key(&self, used: u64, loose: u32) -> u64 {
        if loose == 0 {
            return 0;
        }
        if used == 0 || used == u64::MAX {
            return self.suffix_key(loose as usize);
        }
        // Same fold as `suffix[k]` when `used` is bits `0..k`: outer-of-the
        // used set first, innermost last (`intern_ctx_id` extends with the
        // new innermost).
        let n = self.tys.len();
        let mut id = 0u64;
        for i in (0..64u32).rev() {
            if used & (1u64 << i) == 0 {
                continue;
            }
            if (i as usize) >= n {
                return self.suffix_key(loose as usize);
            }
            let ty_ptr = Rc::as_ptr(&self.tys[n - 1 - i as usize]) as usize;
            id = intern_ctx_id(id, ty_ptr);
        }
        id
    }

    fn suffix_key(&self, k: usize) -> u64 {
        let k = k.min(self.tys.len());
        self.suffix.get(k).copied().unwrap_or(self.id)
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

pub(crate) fn expr_dag_size(e: &Expr, cap: u32) -> u32 {
    let mut seen: rustc_hash::FxHashSet<usize> = rustc_hash::FxHashSet::default();
    let mut stack = vec![e.clone()];
    while let Some(x) = stack.pop() {
        let p = Rc::as_ptr(&x) as usize;
        if !seen.insert(p) {
            continue;
        }
        if seen.len() as u32 >= cap {
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
    seen.len() as u32
}

fn local_ty(ctx: &Ctx, i: u32) -> Option<Expr> {
    let n = ctx.len();
    if (i as usize) >= n {
        return None;
    }
    let raw = &ctx[n - 1 - i as usize];
    Some(expr::shift(raw, i as i32 + 1, 0))
}

/// Maximum nesting depth explored by the nested-positivity check before it
/// declines. Real Lean nesting is shallow (List/Array/Prod wrappers).
const NESTED_POSITIVITY_DEPTH: usize = 16;

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
            eq_related_defs: RefCell::new(Vec::new()),
            eq_arg_heads: RefCell::new(Vec::new()),
        }
    }

    fn ptr_key(e: &Expr) -> usize {
        Rc::as_ptr(e) as usize
    }

    fn whnf_cache_key(ctx: &Ctx, e: &Expr) -> (u64, usize) {
        // Closed terms are context-free. Open terms (K-like `Eq.rec`/`True.rec`
        // of a bvar major) infer the major's type, so the key includes `ctx.id`.
        let ctx_key = if expr::is_closed(e) { 0 } else { ctx.id };
        (ctx_key, Self::ptr_key(e))
    }

    fn insert_defeq(&self, key: (u64, usize, usize), r: bool) {
        if !CORE_ABORTED.with(|a| a.get()) {
            self.defeq_cache.borrow_mut().insert(key, r);
        }
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
        // Drop the previous decl's subst/ctx intern before any WHNF/shape
        // probe. Those maps otherwise hold one extra decl of residue while
        // `type_is_multiarg_prop_structure` runs.
        expr::clear_subst_memos();
        CTX_IDS.with(|m| m.borrow_mut().clear());
        CTX_NEXT.with(|c| c.set(1));
        CORE_ABORTED.with(|a| a.set(false));
        crate::stats::set_theorem_delta_scope(self.name_str(name));
        if std::env::var_os("KIOTA_DEBUG").is_some() && self.name_str(name).contains("_mutual") {
            eprintln!("CHECKING {}", self.name_str(name));
            let _ = std::io::Write::flush(&mut std::io::stderr());
        }
        if std::env::var_os("KIOTA_DUMP_PSIGMA").is_some()
            && self.name_str(name).contains("toGraphviz.go._unary.eq_def")
        {
            for (i, nm) in self.names.iter().enumerate() {
                let s = nm.as_str();
                if s == "PSigma" {
                    match self.env.get(i as u32) {
                        Some(ConstantInfo::InductiveType {
                            is_rec,
                            num_indices,
                            ctors,
                            ..
                        }) => eprintln!(
                            "DUMP PSigma is_rec={is_rec} nidx={num_indices} nctors={} non_rec={}",
                            ctors.len(),
                            self.is_non_rec_structure(i as u32)
                        ),
                        other => eprintln!("DUMP PSigma not inductive {other:?}"),
                    }
                }
                if s == "PSigma.casesOn" {
                    match self.env.get(i as u32) {
                        Some(ConstantInfo::Def { hints, value, .. }) => {
                            eprintln!(
                                "DUMP casesOn hints={hints:?} val={}",
                                self.pp_budget(value, 10)
                            );
                        }
                        other => eprintln!("DUMP casesOn {other:?}"),
                    }
                }
                if s.ends_with("StateT.bind.match_1") || s == "StateT.bind.match_1"
                    || s == "Bind.bind"
                    || s == "Monad.toBind"
                    || s == "StateT.bind"
                    || s == "StateT.instMonad"
                    || s.ends_with(".Bind.bind")
                    || s.ends_with(".StateT.bind")
                    || s.ends_with(".StateT.instMonad")
                {
                    match self.env.get(i as u32) {
                        Some(ConstantInfo::Def { hints, value, .. }) => {
                            eprintln!(
                                "DUMP {s} Def hints={hints:?} sz={} val={}",
                                expr_size_capped(value, 20_000),
                                self.pp_budget(value, 12)
                            );
                        }
                        other => eprintln!("DUMP {s} {other:?}"),
                    }
                }
            }
        }
        self.fuel_nat_peels.set(0);
        *self.fuel_nat_last.borrow_mut() = None;
        self.decl_value_size.set(
            ci.value()
                .map(|v| expr_size_capped(v, 200_000))
                .unwrap_or(0),
        );
        if std::env::var_os("KIOTA_DAG_LOG").is_some() {
            let tree = ci
                .value()
                .map(|v| expr_size_capped(v, 2_000_000))
                .unwrap_or(0);
            let dag = ci.value().map(|v| expr_dag_size(v, 2_000_000)).unwrap_or(0);
            let tdag = expr_dag_size(ci.typ(), 50_000);
            eprintln!(
                "DAG {kind} tree={tree} dag={dag} tydag={tdag} intern={} {}",
                expr::intern_node_count(),
                self.name_str(name)
            );
            eprintln!("TYPEHEAD {kind} {}", self.pp_budget(ci.typ(), 80));
            if let Some(v) = ci.value() {
                let mut cur = v.clone();
                let mut lams = 0u32;
                loop {
                    match &**cur {
                        ExprData::Lam(_, _, b) => {
                            lams += 1;
                            cur = b.clone();
                        }
                        _ => break,
                    }
                }
                let (h, args) = expr::unfold_apps(&cur);
                eprintln!(
                    "VALUEHEAD lams={lams} nargs={} dag={} head={}",
                    args.len(),
                    expr_dag_size(&cur, 200_000),
                    self.pp_budget(&h, 50)
                );
            }
            let _ = std::io::Write::flush(&mut std::io::stderr());
        }
        let multi = kind == "theorem" && self.type_is_multiarg_prop_structure(ci.typ());
        self.checking_prop_structure.set(multi);
        self.checking_simple_prop_inductive.set(
            kind == "theorem" && !multi && self.type_is_unit_ctor_zero_index_prop(ci.typ()),
        );
        self.eq_related_defs.borrow_mut().clear();
        self.eq_arg_heads.borrow_mut().clear();
        self.eq_side_def_size.set(0);
        if std::env::var_os("KIOTA_RELATED_LOG").is_some() && kind == "theorem" {
            let mut rel = self.eq_related_defs.borrow_mut();
            self.fill_eq_related_defs(ci.typ(), &mut rel);
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
        if std::env::var_os("KIOTA_RELATED_LOG").is_some() {
            let rel = self.eq_related_defs.borrow();
            let heads = self.eq_arg_heads.borrow();
            if !rel.is_empty() || !heads.is_empty() {
                eprint!("RELATED {} heads=", self.name_str(name));
                for n in heads.iter() {
                    let sz = match self.env.get(*n) {
                        Some(ConstantInfo::Def { value, .. }) => {
                            expr_size_capped(value, 200_000)
                        }
                        _ => 0,
                    };
                    eprint!("{}:{sz} ", self.name_str(*n));
                }
                eprint!("rel=");
                for n in rel.iter() {
                    let sz = match self.env.get(*n) {
                        Some(ConstantInfo::Def { value, .. }) => {
                            expr_size_capped(value, 200_000)
                        }
                        _ => 0,
                    };
                    eprint!("{}:{sz} ", self.name_str(*n));
                }
                eprintln!();
            }
        }
        // Pointer-keyed WHNF/defeq/infer caches are only useful inside one
        // declaration. Keeping them across decls is how `#3491`–`#3495`
        // grew from ~0.9 GB to multi-GB before the next omega proof.
        // `unfold_cache` is keyed by (const, levels) and is reused.
        expr::clear_subst_memos();
        CTX_IDS.with(|m| m.borrow_mut().clear());
        CTX_NEXT.with(|c| c.set(1));
        self.whnf_cache.borrow_mut().clear();
        self.whnf_core_cache.borrow_mut().clear();
        self.defeq_cache.borrow_mut().clear();
        self.infer_cache.borrow_mut().clear();
        if std::env::var_os("KIOTA_TRACE_DECL").is_some() {
            eprintln!("DECL {kind} {}", self.name_str(name));
        }
        let decl_inst0 = crate::stats::inst_nodes();
        let decl_whnf0 = crate::stats::whnf_calls();
        let decl_intern0 = expr::intern_calls();
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
            let vt = self.infer_type(&ctx, value)?;
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
            let dic = expr::intern_calls() - decl_intern0;
            if di > 100_000 || dw > 1_000_000 || dic > 100_000 {
                eprintln!(
                    "DECLSTATS {} inst=+{} whnf=+{} intern_calls=+{} nodes={}",
                    self.name_str(name),
                    di,
                    dw,
                    dic,
                    expr::intern_node_count()
                );
            }
        }
        Ok(())
    }

    // ---------------- Universe / sort helpers ----------------

    /// beta/iota, `abbrev`, and small Regular. Not `countKnown.go`.
    fn whnf_abbrev(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let mut cur = e.clone();
        loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            let ExprData::Const(n, us) = &**head else {
                return Ok(core);
            };
            if !self.eager_whnf_unfolds(*n) {
                return Ok(core);
            }
            let Some(unfolded) = self.unfold_def(*n, us)? else {
                return Ok(core);
            };
            let (_, args) = expr::unfold_apps(&core);
            let next = expr::apps(unfolded, &args);
            if Rc::ptr_eq(&next, &cur) {
                return Ok(core);
            }
            cur = next;
        }
    }

    /// Lean `ensure_pi`/`ensure_sort`: WHNF-core, then delta until Pi/Sort.
    /// Regular values stay folded in `whnf`; types that wrap a Pi still reduce.
    fn reduce_for_ensure(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let mut w = self.whnf(ctx, e)?;
        for _ in 0..2048 {
            match &**w {
                ExprData::Pi(_, _, _) | ExprData::Sort(_) => return Ok(w),
                _ => {}
            }
            let (head, args) = expr::unfold_apps(&w);
            let ExprData::Const(n, us) = &**head else {
                return Ok(w);
            };
            let Some(unfolded) = self.unfold_def(*n, us)? else {
                return Ok(w);
            };
            let next = expr::apps(unfolded, &args);
            let core = self.whnf_core(ctx, &next)?;
            if Rc::ptr_eq(&core, &w) {
                return Ok(w);
            }
            w = core;
        }
        decline("ensure reduction depth limit")
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
        // Closed → 0. Open `loose = k` → k innermost binders, not the full
        // telescope: a 34k DAG with one loose bvar must not re-Check under
        // every extra PSigma/Acc motive (`._unary` well-founded proofs).
        let ctx_key = ctx.term_ctx_key(e);
        let key = (ctx_key, Self::ptr_key(e));
        let infer_only = self.infer_only.get();
        if let Some((t, checked)) = self.infer_cache.borrow().get(&key) {
            if infer_only || *checked {
                crate::stats::infer_hit();
                return Ok(t.clone());
            }
        }
        let t = self.infer_type_uncached(ctx, e)?;
        let checked = !self.infer_only.get();
        {
            let mut cache = self.infer_cache.borrow_mut();
            match cache.get_mut(&key) {
                Some((old, was_checked)) if checked && !*was_checked => {
                    *old = t.clone();
                    *was_checked = true;
                }
                Some((_, was_checked)) if *was_checked => {}
                Some((old, _)) => *old = t.clone(),
                None => {
                    cache.insert(key, (t.clone(), checked));
                }
            }
        }
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
                // Lean `check` infers every App argument. InferOnly is only
                // for PI (`proofs_of_same_prop`) on already-checked terms.
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
            Some(n) if self.nat_ctors().is_some() => Ok(expr::const_(n, vec![])),
            Some(_) => reject("Nat literal used with a malformed native Nat declaration"),
            None => decline("Nat literal used but Nat type unavailable"),
        }
    }
    fn string_type(&self) -> R<Expr> {
        match self.string_ref {
            Some(n)
                if matches!(
                    self.env.get(n),
                    Some(ConstantInfo::InductiveType {
                        level_params,
                        typ,
                        num_params: 0,
                        num_indices: 0,
                        all,
                        ctors,
                        is_unsafe: false,
                        ..
                    }) if self.name_str(n) == "String"
                        && level_params.is_empty()
                        && **typ == *expr::sort(level::succ(level::zero()))
                        && all.as_slice() == [n]
                        && !ctors.is_empty()
                ) => Ok(expr::const_(n, vec![])),
            Some(_) => reject("String literal used with a malformed native String declaration"),
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
            let (_, prior_dom, body) = self.ensure_pi(ctx, &ct2)?;
            // Lean permits proof projections from a Prop structure only up to
            // the first *dependent* data field.  A later proof field is still
            // forbidden even when its own type is Prop: substituting a
            // projection of data out of a proof would already violate proof
            // irrelevance.  `body` is under the current field binder, so bvar
            // 0 records exactly that dependency.
            if self.is_prop_determinate(ctx, &vtw)?
                && Self::occurs_bvar(&body, 0)
                && !self.is_prop(ctx, &prior_dom)?
            {
                return reject("cannot project past a dependent Type field from a Prop structure");
            }
            let proj_i = expr::proj(sname, i, v.clone());
            ct2 = expr::instantiate1(&body, &proj_i);
        }
        let (_, dom, _body) = self.ensure_pi(ctx, &ct2)?;
        if self.is_prop_determinate(ctx, &vtw)? {
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
        let Some(ConstantInfo::InductiveType {
            level_params,
            typ,
            num_params,
            num_indices,
            all,
            ctors,
            is_rec,
            is_unsafe,
        }) = self.env.get(n)
        else {
            return None;
        };
        if self.name_str(n) != "Nat"
            || !level_params.is_empty()
            || **typ != *expr::sort(level::succ(level::zero()))
            || *num_params != 0
            || *num_indices != 0
            || all.as_slice() != [n]
            || ctors.len() != 2
            || !*is_rec
            || *is_unsafe
        {
            return None;
        }
        let (zero, succ) = (ctors[0], ctors[1]);
        let nat = expr::const_(n, vec![]);
        let succ_ty = expr::pi(expr::BinderInfo::Default, nat.clone(), nat.clone());
        let zero_ok = matches!(
            self.env.get(zero),
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                induct,
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            }) if self.name_str(zero) == "Nat.zero" && level_params.is_empty() && **typ == *nat && *induct == n
        );
        let succ_ok = matches!(
            self.env.get(succ),
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                induct,
                cidx: 1,
                num_params: 0,
                num_fields: 1,
                is_unsafe: false,
            }) if self.name_str(succ) == "Nat.succ" && level_params.is_empty() && **typ == *succ_ty && *induct == n
        );
        (zero_ok && succ_ok).then_some((zero, succ))
    }

    fn nat_numeral_value_whnf(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigUint>> {
        let Some((zero, succ)) = self.nat_ctors() else {
            return Ok(None);
        };
        let mut cur = self.whnf(ctx, e)?;
        let mut offset = BigUint::from(0u32);
        for _ in 0..256 {
            if let Some(n) = nat::as_lit(&cur) {
                return Ok(Some(n + &offset));
            }
            match &**cur {
                ExprData::Const(n, us) if *n == zero && us.is_empty() => {
                    return Ok(Some(offset));
                }
                ExprData::App(f, a)
                    if matches!(&***f, ExprData::Const(n, us) if *n == succ && us.is_empty()) =>
                {
                    offset += 1u32;
                    cur = self.whnf(ctx, a)?;
                }
                _ => return Ok(None),
            }
        }
        Ok(None)
    }

    fn bool_ctors(&self) -> Option<(u32, u32)> {
        let bool_name = self
            .names
            .iter()
            .position(|s| s.as_str() == "Bool")? as u32;
        let Some(ConstantInfo::InductiveType {
            level_params,
            typ,
            num_params,
            num_indices,
            all,
            ctors,
            is_rec,
            is_unsafe,
        }) = self.env.get(bool_name)
        else {
            return None;
        };
        if !level_params.is_empty()
            || **typ != *expr::sort(level::succ(level::zero()))
            || *num_params != 0
            || *num_indices != 0
            || all.as_slice() != [bool_name]
            || ctors.len() != 2
            || *is_rec
            || *is_unsafe
        {
            return None;
        }
        let (false_name, true_name) = (ctors[0], ctors[1]);
        let bool_ty = expr::const_(bool_name, vec![]);
        let ctor_ok = |name: u32, expected: &str, cidx: u32| {
            matches!(
                self.env.get(name),
                Some(ConstantInfo::Constructor {
                    level_params,
                    typ,
                    induct,
                    cidx: actual_cidx,
                    num_params: 0,
                    num_fields: 0,
                    is_unsafe: false,
                }) if self.name_str(name) == expected
                    && level_params.is_empty()
                    && **typ == *bool_ty
                    && *induct == bool_name
                    && *actual_cidx == cidx
            )
        };
        (ctor_ok(false_name, "Bool.false", 0) && ctor_ok(true_name, "Bool.true", 1))
            .then_some((false_name, true_name))
    }

    /// A standalone export does not inherit Lean's trusted bootstrap
    /// environment. Before mirroring a native Nat reducer, establish its
    /// defining equations using ordinary delta/beta/iota reduction on the
    /// already checked declaration body.
    pub fn authenticate_native_nat_decl(&self, n: u32) -> R<bool> {
        let name = self.name_str(n);
        if !matches!(
            name,
            "Nat.add" | "Nat.mul" | "Nat.sub" | "Nat.pow" | "Nat.beq" | "Nat.ble"
        ) {
            return Ok(false);
        }
        if !matches!(
            self.env.get(n),
            Some(ConstantInfo::Def {
                level_params,
                is_unsafe: false,
                ..
            }) if level_params.is_empty()
        ) {
            return Ok(false);
        }
        let Some((zero_name, succ_name)) = self.nat_ctors() else {
            return Ok(false);
        };
        let nat_ty = expr::const_(self.nat_ref.unwrap(), vec![]);
        let zero = expr::const_(zero_name, vec![]);
        let succ = |a: Expr| expr::app(expr::const_(succ_name, vec![]), a);
        let op = |a: Expr, b: Expr| expr::apps(expr::const_(n, vec![]), &[a, b]);
        let mut ctx = Ctx::new();
        ctx.push(nat_ty.clone());
        ctx.push(nat_ty);
        let x = expr::bvar(1);
        let y = expr::bvar(0);
        let sx = succ(x.clone());
        let sy = succ(y.clone());

        let equations: Vec<(Expr, Expr)> = match name {
            "Nat.add" => vec![
                (op(x.clone(), zero.clone()), x.clone()),
                (op(x.clone(), sy.clone()), succ(op(x.clone(), y.clone()))),
            ],
            "Nat.mul" => {
                let Some(add_name) = self
                    .env
                    .native_nat_ops
                    .iter()
                    .copied()
                    .find(|m| self.name_str(*m) == "Nat.add")
                else {
                    return Ok(false);
                };
                let add = |a: Expr, b: Expr| {
                    expr::apps(expr::const_(add_name, vec![]), &[a, b])
                };
                vec![
                    (op(x.clone(), zero.clone()), zero.clone()),
                    (
                        op(x.clone(), sy.clone()),
                        add(op(x.clone(), y.clone()), x.clone()),
                    ),
                ]
            }
            "Nat.sub" => vec![
                (op(x.clone(), zero.clone()), x.clone()),
                (op(zero.clone(), sy.clone()), zero.clone()),
                (op(sx, sy), op(x.clone(), y.clone())),
            ],
            "Nat.pow" => {
                let Some(mul_name) = self
                    .env
                    .native_nat_ops
                    .iter()
                    .copied()
                    .find(|m| self.name_str(*m) == "Nat.mul")
                else {
                    return Ok(false);
                };
                let mul = |a: Expr, b: Expr| {
                    expr::apps(expr::const_(mul_name, vec![]), &[a, b])
                };
                vec![
                    (op(x.clone(), zero.clone()), expr::lit_nat(1u32.into())),
                    (
                        op(x.clone(), sy),
                        mul(op(x.clone(), y.clone()), x.clone()),
                    ),
                ]
            }
            "Nat.beq" | "Nat.ble" => {
                let Some((false_name, true_name)) = self.bool_ctors() else {
                    return Ok(false);
                };
                let f = expr::const_(false_name, vec![]);
                let t = expr::const_(true_name, vec![]);
                if name == "Nat.beq" {
                    vec![
                        (op(zero.clone(), zero.clone()), t),
                        (op(zero.clone(), sy.clone()), f.clone()),
                        (op(sx.clone(), zero.clone()), f),
                        (op(sx, sy), op(x.clone(), y.clone())),
                    ]
                } else {
                    vec![
                        (op(zero.clone(), y.clone()), t),
                        (op(sx.clone(), zero.clone()), f),
                        (op(sx, sy), op(x.clone(), y.clone())),
                    ]
                }
            }
            _ => unreachable!(),
        };
        for (lhs, rhs) in equations {
            if !self.is_def_eq(&ctx, &lhs, &rhs)? {
                return Ok(false);
            }
        }
        Ok(true)
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
            Err(e) => return decline_or_false(e),
        };
        let tb = match self.infer_type(ctx, b) {
            Ok(t) => t,
            Err(e) => return decline_or_false(e),
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
        let mt = match self.infer_type(ctx, major) {
            Ok(t) => t,
            Err(e) => {
                if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
                    eprintln!(
                        "IOTA to_ctor infer fail major={} err={e:?}",
                        self.pp_budget(major, 8)
                    );
                }
                return Err(e);
            }
        };
        let mtw = self.whnf(ctx, &mt)?;
        // Lean skips Prop structures (`is_prop` of the type). PSigma is Type.
        if self.is_prop(ctx, &mtw)? {
            if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
                eprintln!(
                    "IOTA to_ctor skip Prop structure {} ty={}",
                    self.name_str(tname),
                    self.pp_budget(&mtw, 10)
                );
            }
            return Ok(None);
        }
        let (thead, targs) = expr::unfold_apps(&mtw);
        match &**thead {
            ExprData::Const(n, _) if *n == tname => {
                if targs.len() < num_params as usize {
                    if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
                        eprintln!(
                            "IOTA to_ctor underapplied {} targs={} nparams={}",
                            self.name_str(tname),
                            targs.len(),
                            num_params
                        );
                    }
                    return Ok(None);
                }
                let mut ctor_args: Vec<Expr> = targs[..num_params as usize].to_vec();
                for i in 0..nfields {
                    ctor_args.push(expr::proj(tname, i, major.clone()));
                }
                let _ = params;
                Ok(Some((cname, num_params, ctor_args)))
            }
            other => {
                if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
                    eprintln!(
                        "IOTA to_ctor head mismatch want={} got={} ty={}",
                        self.name_str(tname),
                        match other {
                            ExprData::Const(n, _) => self.name_str(*n).to_string(),
                            ExprData::BVar(i) => format!("#{i}"),
                            _ => format!("{other:?}"),
                        },
                        self.pp_budget(&mtw, 12)
                    );
                }
                Ok(None)
            }
        }
    }

    /// Whether `ty` is a proposition (`ty : Prop`), not whether `ty` *is* Prop.
    /// `whnf(Prop) = Sort 0` so a Sort is a universe (`Prop : Type`); PI must
    /// not identify `True` with `False`. Prop inductives, axioms `P : Prop`,
    /// and Pis into those count. Reads the constant's telescope, not `infer_type`
    /// of `ty` (that re-entered Check of huge type spines from PI).
    /// `is_prop`, but "cannot decide" is an error rather than `false`.
    ///
    /// `is_prop` routes a Reject/Other through `decline_or_false`, yielding
    /// `Ok(false)`. That is safe wherever a `true` answer merely *enables* a
    /// shortcut (proof irrelevance, ι skips). At a **restrictive** gate the
    /// polarity flips: a spurious `false` switches the restriction off. For
    /// projections that would admit data out of a proof, so decline instead
    /// of guessing.
    fn is_prop_determinate(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        // Unlike `is_prop`, this propagates instead of swallowing.
        let w = self.whnf(ctx, ty)?;
        self.is_prop(ctx, &w)
    }

    fn is_prop(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        let w = match self.whnf(ctx, ty) {
            Ok(w) => w,
            Err(e) => return decline_or_false(e),
        };
        match &**w {
            ExprData::Sort(_) => Ok(false),
            ExprData::BVar(i) => {
                let Some(t) = local_ty(ctx, *i) else {
                    return Ok(false);
                };
                let tw = match self.whnf(ctx, &t) {
                    Ok(x) => x,
                    Err(e) => return decline_or_false(e),
                };
                Ok(matches!(&**tw, ExprData::Sort(l) if level::is_def_eq(l, &level::zero())))
            }
            ExprData::Pi(_, dom, body) => {
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(dom.clone());
                self.is_prop(&ctx2, body)
            }
            _ => {
                let (h, args) = expr::unfold_apps(&w);
                let ExprData::Const(n, us) = &**h else {
                    return self.is_prop_by_infer(ctx, &w);
                };
                if let Some(ConstantInfo::InductiveType {
                    typ,
                    num_params,
                    level_params,
                    ..
                }) = self.env.get(*n)
                {
                    if (args.len() as u32) >= *num_params {
                        let subst = level::subst_map(level_params, us);
                        let instantiated = expr::instantiate_level_params(typ, &subst);
                        return Ok(self.sort_codomain_is_prop(&instantiated));
                    }
                }
                let Some(cty) = self.const_typ(*n) else {
                    return self.is_prop_by_infer(ctx, &w);
                };
                if self.telescope_codomain_is_prop(cty, args.len()) {
                    return Ok(true);
                }
                self.is_prop_by_infer(ctx, &w)
            }
        }
    }

    /// InferOnly typeof. Check-mode infer here re-entered PI on huge type
    /// spines (`blastAdd`). Lean `is_prop` uses `infer`, not `check`.
    fn is_prop_by_infer(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        self.with_infer_only(|| match self.infer_type(ctx, ty) {
            Ok(s) => match self.ensure_sort(ctx, &s) {
                Ok(l) => Ok(level::is_def_eq(&l, &level::zero())),
                Err(e) => decline_or_false(e),
            },
            Err(e) => decline_or_false(e),
        })
    }

    fn telescope_codomain_is_prop(&self, typ: &Expr, args: usize) -> bool {
        let mut t = typ.clone();
        for _ in 0..args {
            match &**t {
                ExprData::Pi(_, _, b) => t = b.clone(),
                _ => return false,
            }
        }
        matches!(&**t, ExprData::Sort(l) if level::is_def_eq(l, &level::zero()))
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
    /// Size is not a proof test: class instances are large Regular *proofs*
    /// of a Prop (`#18000` `LawfulVecOperator`). `infer_type` of a const uses
    /// the declared type, not the body — skipping those forced pairwise of
    /// nested `mk` fields.
    fn obviously_not_proof(&self, e: &Expr) -> bool {
        match &***e {
            // Lams can be proofs (`True → True`, `fun α => Mk …` class
            // instances). Skipping PI on them forced lam-congruence of
            // `#18041` nested `LawfulOperator` bodies.
            ExprData::Sort(_) | ExprData::Pi(_, _, _) | ExprData::Lit(_) => true,
            _ => {
                let (h, args) = expr::unfold_apps(e);
                let ExprData::Const(n, _) = &**h else {
                    return false;
                };
                match self.env.get(*n) {
                    Some(ConstantInfo::InductiveType {
                        typ, num_params, ..
                    }) if (args.len() as u32) >= *num_params => !self.sort_codomain_is_prop(typ),
                    Some(ConstantInfo::Constructor { induct, .. }) => match self.env.get(*induct)
                    {
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
            Err(e) => return decline_or_false(e),
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
        crate::stats::k_pi_infer_only();
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
            Err(e) => return decline_or_false(e),
        };
        let prop_a = self.is_prop(ctx, &ta)?;
        if !prop_a {
            return Ok(false);
        }
        let tb = match self.infer_type(ctx, b) {
            Ok(t) => t,
            Err(e) => return decline_or_false(e),
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
        // Prop-ctor spines and class-instance defs (`LawfulOperator.mk`,
        // `instLawful*`) must use `defeq_args` so proof fields/args are
        // skipped. Pairwise of those is 7^depth (`#18000`, `#18041`).
        if let ConstantInfo::Constructor { induct, .. } = ci {
            if let Some(ConstantInfo::InductiveType { typ, .. }) = self.env.get(*induct) {
                if self.sort_codomain_is_prop(typ) {
                    return true;
                }
            }
        }
        if let ConstantInfo::InductiveType { typ, .. } = ci {
            if self.sort_codomain_is_prop(typ) {
                return true;
            }
        }
        if self.type_is_unit_ctor_zero_index_prop(ci.typ())
            || self.type_is_multiarg_prop_structure(ci.typ())
            || self.peel_to_inductive_head(ci.typ()).is_some_and(|(_, _, _, _, ity)| {
                self.sort_codomain_is_prop(ity)
            })
        {
            return true;
        }
        let mut t = ci.typ().clone();
        let empty = Ctx::new();
        for _ in 0..64 {
            match &**t {
                ExprData::Pi(_, dom, body) => {
                    // On an incomplete probe, take the typed argument path.
                    // `false` selects raw pairwise comparison and can turn a
                    // depth limit into a cached negative result.
                    if self.domain_is_prop_inductive(&empty, dom).unwrap_or(true) {
                        return true;
                    }
                    t = body.clone();
                }
                _ => match self.whnf(&empty, &t) {
                    Ok(w) if !Rc::ptr_eq(&w, &t) => t = w,
                    Ok(_) => return false,
                    Err(_) => return true,
                },
            }
        }
        false
    }

    fn trace_pair(kind: &str, name: &str, na: usize, has_pr: bool) {
        thread_local! {
            static N: Cell<u32> = const { Cell::new(0) };
        }
        N.with(|c| {
            let n = c.get();
            if n < 40 {
                c.set(n + 1);
                eprintln!("PAIR {kind} {name} na={na} proof_arg={has_pr}");
            }
        });
    }

    fn with_fresh_app_cong<T>(&self, f: impl FnOnce() -> T) -> T {
        let old = APP_CONG_DEPTH.with(|d| d.replace(0));
        let r = f();
        APP_CONG_DEPTH.with(|d| d.set(old));
        r
    }

    fn app_spines_congruent(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
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
                let has_pr = self.const_has_proof_arg(*n1);
                if std::env::var_os("KIOTA_TRACE_PAIR").is_some() && a1.len() >= 3 {
                    Self::trace_pair("core", self.name_str(*n1), a1.len(), has_pr);
                }
                let r = if has_pr {
                    match self.infer_const(*n1, u1) {
                        Ok(fn_ty) => self.defeq_args(ctx, &fn_ty, &a1, &a2)?,
                        Err(_) => self.pairwise_args(ctx, &a1, &a2)?,
                    }
                } else {
                    self.pairwise_args(ctx, &a1, &a2)?
                };
                if !r && std::env::var_os("KIOTA_TRACE_EQ").is_some() && a1.len() >= 4 {
                    eprintln!(
                        "EQCORE fail {} na={}",
                        self.name_str(*n1),
                        a1.len()
                    );
                }
                return Ok(r);
            }
            return Ok(false);
        }
        if a1.len() != a2.len() {
            return Ok(false);
        }
        let head_eq = Rc::ptr_eq(&h1, &h2)
            || (!matches!(&**h1, ExprData::Const(..))
                && !matches!(&**h2, ExprData::Const(..))
                && self.is_def_eq(ctx, &h1, &h2)?);
        if !head_eq {
            return Ok(false);
        }
        if let ExprData::Const(n, us) = &**h1 {
            if self.const_has_proof_arg(*n) {
                return match self.infer_const(*n, us) {
                    Ok(fn_ty) => self.defeq_args(ctx, &fn_ty, &a1, &a2),
                    Err(_) => self.pairwise_args(ctx, &a1, &a2),
                };
            }
        }
        self.pairwise_args(ctx, &a1, &a2)
    }

    fn pairwise_args(&self, ctx: &Ctx, a1: &[Expr], a2: &[Expr]) -> R<bool> {
        if a1.len() != a2.len() {
            return Ok(false);
        }
        for (i, (x, y)) in a1.iter().zip(a2.iter()).enumerate() {
            if !self.is_def_eq(ctx, x, y)? {
                if std::env::var_os("KIOTA_TRACE_EQ").is_some() {
                    eprintln!(
                        "EQPAIR fail i={i}/{} a={} b={}",
                        a1.len(),
                        self.pp_budget(x, 16),
                        self.pp_budget(y, 16)
                    );
                }
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
            if self.domain_is_prop_inductive(ctx, &dom)? || self.is_prop(ctx, &dom)?
            {
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
        if depth > CONV_DEPTH {
            WHNF_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            if depth == CONV_DEPTH + 1 && std::env::var_os("KIOTA_DEBUG").is_some() {
                eprintln!("WHNF_DEPTH {}", self.pp_budget(e, 50));
            }
            return decline("WHNF depth limit");
        }
        let r = self.whnf_inner(ctx, e);
        WHNF_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        r
    }

    fn whnf_inner(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        crate::stats::whnf_call();
        if crate::stats::enabled() {
            let n = crate::stats::whnf_calls();
            if n > 0 && n % 50_000 == 0 {
                eprintln!(
                    "MEM whnf={n} defeq={} infer={} intern={}",
                    crate::stats::defeq_calls(),
                    crate::stats::infer_calls(),
                    expr::intern_node_count(),
                );
                let _ = std::io::Write::flush(&mut std::io::stderr());
            }
        }
        let k = Self::whnf_cache_key(ctx, e);
        if let Some(r) = self.whnf_cache.borrow().get(&k) {
            return Ok(r.clone());
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
        // Abort is per-`whnf` call. Leaving CORE_ABORTED set poisoned later
        // unfolds in the same decl (`Int8.toInt_toInt32` declined after a
        // deep stuck recursor, then a shallow β-redex was treated as the
        // abort result).
        let aborted = CORE_ABORTED.with(|a| a.replace(false));
        if aborted {
            if self.is_whnf_core_redex(&r) {
                return decline(format!(
                    "WHNF core depth limit: {}",
                    self.pp_budget(&r, 12)
                ));
            }
            return Ok(r);
        }
        self.whnf_cache.borrow_mut().insert(k, r.clone());
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
        // Recursor spines and *large* Regulars must WHNF/δ/ι first.
        // Unreduced pairwise of `mkGateCached` walks AIG `BinaryInput.mk`
        // as a tree (`#18041`). Abbrev Acc wrappers still congruence.
        if matches!(self.env.get(*n1), Some(ConstantInfo::Recursor { .. })) {
            return Ok(false);
        }
        // Type-structure ctors (`BinaryInput.mk`): unreduced field-pairwise
        // is a tree walk of AIG DAGs. WHNF+δ first intern-shares the spine.
        if let Some(ConstantInfo::Constructor { induct, .. }) = self.env.get(*n1) {
            if let Some(ConstantInfo::InductiveType {
                typ,
                ctors,
                num_indices,
                is_rec,
                ..
            }) = self.env.get(*induct)
            {
                if ctors.len() == 1 && *num_indices == 0 && !*is_rec && !self.sort_codomain_is_prop(typ)
                {
                    return Ok(false);
                }
            }
        }
        if !u1.iter().zip(u2.iter()).all(|(x, y)| level::is_def_eq(x, y)) {
            return Ok(false);
        }
        let eq_trace = std::env::var_os("KIOTA_TRACE_LINEAR").is_some()
            && a1.iter().chain(a2.iter()).any(|e| {
                self.pp_budget(e, 40).contains("norm_eq_cert")
            });
        let has_pr = self.const_has_proof_arg(*n1);
        if std::env::var_os("KIOTA_TRACE_PAIR").is_some() && a1.len() >= 3 {
            Self::trace_pair("unreduced", self.name_str(*n1), a1.len(), has_pr);
        }
        let r = if has_pr {
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
        if !r && std::env::var_os("KIOTA_TRACE_EQ").is_some() && a1.len() >= 4 {
            eprintln!(
                "EQSPINE fail {} na={} a4={} b4={}",
                self.name_str(*n1),
                a1.len(),
                self.pp_budget(&a1[a1.len() - 1], 10),
                self.pp_budget(&a2[a2.len() - 1], 10)
            );
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
                typ,
                is_rec,
                ctors,
                ..
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
    /// True when `whnf_core` still has a β/ζ/proj redex. Delta/ι are the
    /// outer `whnf` / `try_iota` steps; a recursor app with a stuck major
    /// is already core-WHNF. Such a result is never cached after an abort.
    fn is_whnf_core_redex(&self, e: &Expr) -> bool {
        match &***e {
            ExprData::Let(_, _, _) => true,
            ExprData::Proj(_, _, _) => true,
            ExprData::App(_, _) => {
                let (head, _) = expr::unfold_apps(e);
                matches!(
                    &**head,
                    ExprData::Lam(_, _, _) | ExprData::Let(_, _, _) | ExprData::Proj(_, _, _)
                ) || matches!(
                    &**head,
                    ExprData::Const(n, _) if matches!(
                        self.env.get(*n),
                        Some(ConstantInfo::Def { .. })
                            | Some(ConstantInfo::Recursor { .. })
                            | Some(ConstantInfo::Quot { .. })
                    ) || self.env.native_nat_ops.contains(n)
                )
            }
            _ => false,
        }
    }

    fn is_beta_app(e: &Expr) -> bool {
        let (head, args) = expr::unfold_apps(e);
        !args.is_empty() && matches!(&**head, ExprData::Lam(_, _, _))
    }

    fn cheap_zeta(e: &Expr) -> Expr {
        let mut cur = e.clone();
        while let ExprData::Let(_, val, body) = &**cur {
            cur = expr::instantiate1(body, val);
        }
        cur
    }

    fn whnf_core(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        // ζ before the depth cap: a `let` produced by structure ι
        // (`StateT.bind.match_1`) must not freeze as WHNF just because
        // `CORE_DEPTH` is already at CONV_DEPTH.
        let e = Self::cheap_zeta(e);
        let depth = CORE_DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        if depth > CONV_DEPTH {
            CORE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            CORE_ABORTED.with(|a| a.set(true));
            // Do not cache. A potentially reducible term at the cap is not
            // established WHNF, so propagate Decline.
            if std::env::var_os("KIOTA_TRACE_IOTA").is_some()
                || std::env::var_os("KIOTA_TRACE_EQ").is_some()
            {
                eprintln!("CORE_DEPTH abort {}", crate::expr::loose_bvar_range(&e));
            }
            if self.is_whnf_core_redex(&e) {
                return decline(format!(
                    "WHNF core depth limit: {}",
                    self.pp_budget(&e, 12)
                ));
            }
            return Ok(e);
        }
        let k = Self::whnf_cache_key(ctx, &e);
        if let Some(r) = self.whnf_core_cache.borrow().get(&k) {
            CORE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            return Ok(r.clone());
        }
        let r = self.whnf_core_go(ctx, &e);
        CORE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        let r = r?;
        if CORE_ABORTED.with(|a| a.get()) {
            return Ok(r);
        }
        self.whnf_core_cache.borrow_mut().insert(k, r.clone());
        Ok(r)
    }

    fn whnf_core_go(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let mut cur = e.clone();
        loop {
            match &**cur {
                ExprData::App(_, _) => {
                    let (head, args) = expr::unfold_apps(&cur);
                    match &**head {
                        // Lean `whnf_core` on App first `whnf_core`s the function.
                        // A Let head is ζ, then the args are reapplied:
                        //   WHNF ((let x := v; f) a₁ … aₙ) = WHNF (f[v] a₁ … aₙ)
                        // Without this, `StateT.bind.match_1` ι yields a `let`
                        // that stuck as App(Let, minor), so Bind.bind minors
                        // (`p.1` vs unpacked) never converted (#81930).
                        ExprData::Let(_, _, _) => {
                            cur = expr::apps(Self::cheap_zeta(&head), &args);
                            continue;
                        }
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
                            let mut vw = self.whnf(ctx, v)?;
                            if let Some(u) = self.try_unfold_const_head(&vw)? {
                                vw = self.whnf_core(ctx, &u)?;
                            }
                            let (phead, pargs) = expr::unfold_apps(&vw);
                            if let ExprData::Const(cname, _us) = &**phead {
                                if let Some(ConstantInfo::Constructor {
                                    num_params,
                                    induct,
                                    ..
                                }) = self.env.get(*cname)
                                {
                                    if *induct == *sname {
                                        let fi = (*num_params + *idx) as usize;
                                        if fi < pargs.len() {
                                            cur = expr::apps(pargs[fi].clone(), &args);
                                            continue;
                                        }
                                    }
                                }
                            }
                            if let ExprData::Lit(Lit::Str(s)) = &**vw {
                                if *idx == 0 && self.authenticated_native_string(*sname) {
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
                            // These shortcuts implement library definitions,
                            // not kernel reduction rules. A checked export may
                            // bind the same canonical name to a different
                            // definition, so names and declaration kinds do not
                            // authenticate them. They are available only for an
                            // explicitly trusted input corpus; the default
                            // checker stays on kernel-derived reductions.
                            let trusted_library_oracles =
                                std::env::var_os("KIOTA_TRUST_LIBRARY_ORACLES").is_some();
                            let authenticated_nat_op = matches!(
                                &**head,
                                ExprData::Const(n, _)
                                    if self.env.native_nat_ops.contains(n)
                                        || (self.name_str(*n) == "Nat.succ"
                                            && self.nat_ctors().is_some())
                            );
                            if trusted_library_oracles || authenticated_nat_op {
                                if let Some(r) = self.try_nat_extension(ctx, &head, &args)? {
                                    crate::stats::n_nat();
                                    cur = r;
                                    continue;
                                }
                            }
                            // These evaluators summarize non-kernel library definitions.
                            // An axiom, opaque constant, constructor, or recursor with the
                            // same name has no such reduction rule. Definitions still need
                            // their bodies authenticated before this gate is a complete
                            // identity check; this prevents declaration-kind substitution.
                            let semantic_def = trusted_library_oracles
                                && matches!(
                                    &**head,
                                    ExprData::Const(n, _)
                                        if matches!(self.env.get(*n), Some(ConstantInfo::Def { .. }))
                                );
                            if semantic_def {
                                if let Some(r) = self.try_omega_combo(ctx, &head, &args)? {
                                    crate::stats::l_omega();
                                    cur = r;
                                    continue;
                                }
                                if let Some(r) = self.try_omega_constraint(ctx, &head, &args)? {
                                    crate::stats::l_omega();
                                    cur = r;
                                    continue;
                                }
                                if let Some(r) = self.try_intlist(ctx, &head, &args)? {
                                    crate::stats::l_omega();
                                    cur = r;
                                    continue;
                                }
                                if let Some(r) = self.try_int_linear(ctx, &head, &args)? {
                                    crate::stats::l_linear();
                                    cur = r;
                                    continue;
                                }
                                if let Some(r) = self.try_comm_ring(ctx, &head, &args)? {
                                    crate::stats::l_commring();
                                    cur = r;
                                    continue;
                                }
                                if let Some(r) = self.try_rat(ctx, &head, &args)? {
                                    crate::stats::l_rat();
                                    cur = r;
                                    continue;
                                }
                            }
                            if trusted_library_oracles {
                                if let Some(r) = self.try_dite(ctx, &head, &args)? {
                                    cur = r;
                                    continue;
                                }
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
                    let mut vw = self.whnf(ctx, v)?;
                    if let Some(u) = self.try_unfold_const_head(&vw)? {
                        vw = self.whnf_core(ctx, &u)?;
                    }
                    let (head, args) = expr::unfold_apps(&vw);
                    if let ExprData::Const(cname, _us) = &**head {
                        if let Some(ConstantInfo::Constructor {
                            num_params,
                            induct,
                            ..
                        }) = self.env.get(*cname)
                        {
                            if *induct == *sname {
                                let fi = (*num_params + *idx) as usize;
                                if fi < args.len() {
                                    cur = args[fi].clone();
                                    continue;
                                }
                            }
                        }
                    }
                    if let ExprData::Lit(Lit::Str(s)) = &**vw {
                        if *idx == 0 && self.authenticated_native_string(*sname) {
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
    fn try_unfold_const_head(&self, e: &Expr) -> R<Option<Expr>> {
        let (h, args) = expr::unfold_apps(e);
        let ExprData::Const(n, us) = &**h else {
            return Ok(None);
        };
        Ok(self.unfold_def(*n, us)?.map(|u| expr::apps(u, &args)))
    }

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

    /// Eager WHNF unfolds Abbrev always and Regular/theorem bodies under this
    /// cap. `Nat.Linear.Poly.cancelAux` is Regular ~664 nodes and must unfold
    /// so `of_denote_eq_cancelAux` typechecks; circuit-sized Regulars stay
    /// folded. `ensure_pi` may one-step unfold a larger Regular wrapping a Pi.
    /// `LawfulVecOperator` shape: Prop, one ctor, no indices, many params,
    /// at least two fields. `Eq` has indices; `And` has 2 params; `Finite`
    /// has one field. No library-name test.
    fn peel_to_inductive_head<'a>(
        &'a self,
        typ: &Expr,
    ) -> Option<(
        u32,
        &'a [u32],
        u32,
        u32,
        &'a Expr,
    )> {
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

    /// Typeclass / structure instance: 1 ctor, no indices, ≥3 params.
    /// `Iterator`/`Finite` match; `Prod`/`PSigma` (2 params) and circuit
    /// `._unary` functions (data-valued Pis) do not.
    fn type_is_packed_structure(&self, typ: &Expr) -> bool {
        let Some((_, ctors, num_indices, num_params, _)) = self.peel_to_inductive_head(typ)
        else {
            return false;
        };
        if ctors.len() != 1 || num_indices != 0 || num_params < 3 {
            return false;
        }
        matches!(
            self.env.get(ctors[0]),
            Some(ConstantInfo::Constructor { num_fields, .. }) if *num_fields >= 1
        )
    }

    fn def_is_packed_structure(&self, n: u32) -> bool {
        match self.env.get(n) {
            Some(ci) => self.type_is_packed_structure(ci.typ()),
            None => false,
        }
    }

    /// `Eq`/`HEq` shape: Prop, one ctor, at least one index. Collects Def
    /// heads on the equated arguments and Defs mentioned in those bodies
    /// (one level).
    fn fill_eq_related_defs(&self, typ: &Expr, out: &mut Vec<u32>) {
        let mut t = typ.clone();
        for _ in 0..64 {
            match &**t {
                ExprData::Pi(_, _, b) => t = b.clone(),
                _ => break,
            }
        }
        let (head, args) = expr::unfold_apps(&t);
        let ExprData::Const(n, _) = &**head else {
            return;
        };
        let Some(ConstantInfo::InductiveType {
            ctors,
            num_indices,
            typ: ity,
            ..
        }) = self.env.get(*n)
        else {
            return;
        };
        if ctors.len() != 1 || *num_indices == 0 || !self.sort_codomain_is_prop(ity) {
            return;
        }
        for a in &args {
            let (h, _) = expr::unfold_apps(a);
            let ExprData::Const(cn, _) = &**h else {
                continue;
            };
            if matches!(self.env.get(*cn), Some(ConstantInfo::Def { .. })) && !out.contains(cn)
            {
                out.push(*cn);
            }
        }
        self.eq_arg_heads.borrow_mut().clone_from(out);
        let mut mentioned = Vec::new();
        self.collect_def_consts(typ, &mut mentioned);
        for m in mentioned {
            let sz = match self.env.get(m) {
                Some(ConstantInfo::Def { value: v, .. }) => expr_size_capped(v, 8_000),
                _ => 0,
            };
            if sz < 4_000 && !out.contains(&m) {
                out.push(m);
            }
        }
        let heads = out.clone();
        for n in &heads {
            if let Some(ConstantInfo::Def { value, .. }) = self.env.get(*n) {
                let mut nested = Vec::new();
                self.collect_def_consts(value, &mut nested);
                for m in nested {
                    let sz = match self.env.get(m) {
                        Some(ConstantInfo::Def { value: v, .. }) => {
                            expr_size_capped(v, 8_000)
                        }
                        _ => 0,
                    };
                    if sz < 4_000 && !out.contains(&m) {
                        out.push(m);
                    }
                }
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
        // Lean `is_delta` = `has_value`, and every `def` has one. Hints only
        // order which side unfolds first in lazy delta (`def_height`); they
        // never make a definition irreducible to the kernel — that is
        // `opaqueDecl`, a different declaration kind. Gating on `Opaque` here
        // hid a recursive constructor field behind `constType` (a `def` with
        // opaque hints), so iota dropped the induction hypothesis
        // (tutorial/053, /121, /122). Nested `Syntax.rec_k` ι is
        // rule-ctor identity + specialization-order rec_group, not a size
        // band. Lazy delta (`is_delta_reducible`) still unfolds theorems
        // that pass the small-body cut.
        match self.env.get(n) {
            Some(ConstantInfo::Def { .. }) => true,
            _ => false,
        }
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
        if is_thm_kind && !crate::stats::theorem_delta_in_scope() {
            crate::stats::c_thm_delta_off();
        }
        // Unset scope is global, but only small theorem bodies unfold
        // (opaque-unless-small). Large proofs stay folded so Check of
        // equation lemmas does not intern-explode or mis-reduce.
        let is_thm = is_thm_kind
            && std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_none()
            && crate::stats::theorem_delta_in_scope()
            && self.delta_body_is_small(n);
        // Lean `is_delta` = `has_value`. WHNF unfolds Abbrev and Regular
        // (`eager_whnf_unfolds`). Lazy delta still unfolds theorems that
        // pass the small-body cut so `Bind.bind inst.1` can reach
        // `StateT.bind` / `match_1`.
        // Reducibility hints are elaborator guidance. Every checked `Def` has
        // a kernel value and is a legal delta target, including a declaration
        // exported with the `opaque` hint. (An `Opaque` declaration is a
        // different environment kind and remains irreducible.)
        let is_def = matches!(self.env.get(n), Some(ConstantInfo::Def { .. }));
        is_def || is_thm
    }

    // ---------------- Definitional equality ----------------

    pub fn is_def_eq(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let depth = DEFEQ_DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        if depth > CONV_DEPTH {
            DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            if depth == CONV_DEPTH + 1 && std::env::var_os("KIOTA_DEBUG").is_some() {
                eprintln!(
                    "DEFEQ_DEPTH a={} b={}",
                    self.pp_budget(a, 50),
                    self.pp_budget(b, 50)
                );
            }
            return decline("defeq depth limit");
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
        // Compare long chains such as `s (s (... z))` iteratively.  Recursive
        // congruence consumes one conversion-stack frame per application and
        // made the 14,520-step Church numeral benchmark hit CONV_DEPTH even
        // though every shared function head is syntactically identical.
        let mut aa = a.clone();
        let mut bb = b.clone();
        let mut peeled = false;
        loop {
            match (&**aa, &**bb) {
                (ExprData::App(fa, xa), ExprData::App(fb, xb))
                    if Rc::ptr_eq(fa, fb) || fa == fb =>
                {
                    aa = xa.clone();
                    bb = xb.clone();
                    peeled = true;
                }
                _ => break,
            }
        }
        if peeled {
            // Congruence proves equality when the tails convert.  A negative
            // tail result is not conclusive because the shared function may
            // erase its argument after delta reduction, so retain the full
            // conversion path in that case.
            if self.is_def_eq(ctx, &aa, &bb)? {
                return Ok(true);
            }
        }
        let (ka, kb) = (Self::ptr_key(a), Self::ptr_key(b));
        let (min_k, max_k) = if ka <= kb { (ka, kb) } else { (kb, ka) };
        // Closed pairs → 0. Open → k innermost binders (`pair_ctx_key`).
        let ctx_key = ctx.pair_ctx_key(a, b);
        let key = (ctx_key, min_k, max_k);
        if let Some(&r) = self.defeq_cache.borrow().get(&key) {
            return Ok(r);
        }
        // Proof irrelevance before app congruence. Typeclass instances are
        // proofs of a Prop (the class). Pairwise of `LawfulVecOperator.mk`
        // (7 args, nested ~15 deep) is a tree walk; PI compares the inferred
        // class types instead. Acc `f 1 a` vs `f 1 (Acc.intro …)` is Bool,
        // so PI is false there and unreduced congruence still runs.
        if self.proofs_of_same_prop(ctx, a, b)? {
            self.insert_defeq(key, true);
            return Ok(true);
        }
        if self.try_unreduced_const_congruence(ctx, a, b)? {
            self.insert_defeq(key, true);
            return Ok(true);
        }
        let aw = self.whnf_for_defeq(ctx, a)?;
        let bw = self.whnf_for_defeq(ctx, b)?;
        if std::env::var_os("KIOTA_TRACE_EQ").is_some() {
            let ha = expr::unfold_apps(a).0;
            if let ExprData::Const(n, _) = &**ha {
                let nm = self.name_str(*n);
                if nm.contains("casesOn") || nm.ends_with(".rec") || nm.contains("match_1") {
                    let hb = expr::unfold_apps(&aw).0;
                    let hbn = match &**hb {
                        ExprData::Const(m, _) => self.name_str(*m).to_string(),
                        ExprData::Lam(_, _, _) => "lam".into(),
                        ExprData::Let(_, _, _) => "let".into(),
                        ExprData::BVar(i) => format!("#{i}"),
                        ExprData::Proj(s, i, _) => format!("proj {}.{}", self.name_str(*s), i),
                        ExprData::Pi(_, _, _) => "pi".into(),
                        _ => format!("{hb:?}"),
                    };
                    eprintln!("WHNFHEAD {nm} -> {hbn}");
                }
            }
        }
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
        let r = self.is_def_eq_core(ctx, &aw, &bw)?;
        // CONV_DEPTH / CORE_DEPTH abort as Decline, not Ok(false), so a stored
        // false is a completed answer. True-only left std `#18000` retrying the
        // same failing pair — 1e9 intern hits, intern size unchanged.
        // Do not cache a result produced under a CORE_DEPTH stuck WHNF.
        self.insert_defeq(key, r);
        Ok(r)
    }

    fn is_def_eq_core(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let r = self.is_def_eq_core_go(ctx, a, b)?;
        if !r && crate::stats::trace_neq() {
            eprintln!("NEQ[{}]  {}   ###   {}", ctx.len(), self.pp_budget(a, 60), self.pp_budget(b, 60));
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
        if matches!(&***a, ExprData::Lit(Lit::Nat(_)))
            || matches!(&***b, ExprData::Lit(Lit::Nat(_)))
        {
            if let (Some(x), Some(y)) = (
                self.nat_numeral_value_whnf(ctx, a)?,
                self.nat_numeral_value_whnf(ctx, b)?,
            ) {
                return Ok(x == y);
            }
        }
        if let Some((zero, succ)) = self.nat_ctors() {
            if let (Some(x), Some(y)) = (
                nat::numeral_value(a, zero, succ),
                nat::numeral_value(b, zero, succ),
            ) {
                return Ok(x == y);
            }
        }
        // One-sided delta can re-enter the core with a fresh zeta/beta redex.
        // Normalize it through the ordinary kernel reduction path before
        // structural spine comparison.
        if let ExprData::Let(_, v, body) = &***a {
            return self.is_def_eq(ctx, &expr::instantiate1(body, v), b);
        }
        if let ExprData::Let(_, v, body) = &***b {
            return self.is_def_eq(ctx, a, &expr::instantiate1(body, v));
        }
        if Self::is_beta_app(a) {
            let w = self.whnf(ctx, a)?;
            if !Rc::ptr_eq(&w, a) {
                return self.is_def_eq(ctx, &w, b);
            }
        }
        if Self::is_beta_app(b) {
            let w = self.whnf(ctx, b)?;
            if !Rc::ptr_eq(&w, b) {
                return self.is_def_eq(ctx, a, &w);
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
                return self.with_fresh_app_cong(|| self.is_def_eq(&ctx2, b1, b2));
            }
            (ExprData::Lam(_, t1, b1), ExprData::Lam(_, t2, b2)) => {
                if !self.is_def_eq(ctx, t1, t2)? {
                    return Ok(false);
                }
                let mut ctx2 = {
                    crate::stats::ctx_clone();
                    ctx.clone()
                };
                ctx2.push(t1.clone());
                return self.with_fresh_app_cong(|| self.is_def_eq(&ctx2, b1, b2));
            }
            (ExprData::App(_, _), ExprData::App(_, _)) => {
                if self.app_spines_congruent(ctx, a, b)? {
                    return Ok(true);
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
                return self.with_fresh_app_cong(|| self.is_def_eq(&ctx2, &a_body, &b_app));
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
                return self.with_fresh_app_cong(|| self.is_def_eq(&ctx2, &a_app, &b_body));
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
                if self.is_delta_reducible(x) {
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
                let rx = self.is_delta_reducible(x);
                let ry = self.is_delta_reducible(y);
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
            (Some(x), None) if self.is_delta_reducible(x) => {
                let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                self.is_def_eq_core(ctx, &ua, b)
            }
            (None, Some(y)) if self.is_delta_reducible(y) => {
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
                    Err(e) => return decline_or_false(e),
                };
                if !self.is_prop(ctx, &ta)? {
                    return Ok(false);
                }
                let tb = match self.infer_type(ctx, b) {
                    Ok(t) => t,
                    Err(e) => return decline_or_false(e),
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

    /// Constructor field types after `num_params`, optionally instantiated.
    /// Used to reconstruct nested `F … I …` owners; not rule `nfields`.
    fn ctor_field_tys(typ: &Expr, num_params: u32, inst: Option<&[Expr]>) -> Vec<Expr> {
        let mut cur = typ.clone();
        let mut peeled = 0u32;
        while peeled < num_params {
            match &**cur {
                ExprData::Pi(_, _, body) => {
                    cur = body.clone();
                    peeled += 1;
                }
                _ => return Vec::new(),
            }
        }
        if let Some(args) = inst {
            let rev: Vec<Expr> = args.iter().rev().cloned().collect();
            cur = expr::instantiate(&cur, &rev);
        }
        let mut fields = Vec::new();
        loop {
            match &**cur {
                ExprData::Pi(_, dom, body) => {
                    fields.push(dom.clone());
                    cur = body.clone();
                }
                _ => break,
            }
        }
        fields
    }

    fn rec_group_all(&self, rname: u32) -> Vec<u32> {
        let mut ts = Vec::new();
        for rec in self.rec_group(rname) {
            if let Some(ConstantInfo::Recursor { all, .. }) = self.env.get(rec) {
                for t in all {
                    if !ts.contains(t) {
                        ts.push(*t);
                    }
                }
            }
        }
        if ts.is_empty() {
            if let Some(ConstantInfo::Recursor { all, .. }) = self.env.get(rname) {
                return all.clone();
            }
        }
        ts
    }

    fn expr_collect_nested(
        &self,
        e: &Expr,
        group: &[u32],
        nested: &mut Vec<u32>,
        work: &mut Vec<Expr>,
        seen: &mut Vec<u32>,
    ) {
        match &***e {
            ExprData::App(_, _) => {
                let (h, args) = expr::unfold_apps(e);
                if let ExprData::Const(n, us) = &**h {
                    self.note_nested_induct(*n, us, &args, group, nested, work, seen);
                }
                match &***e {
                    ExprData::App(f, a) => {
                        self.expr_collect_nested(f, group, nested, work, seen);
                        self.expr_collect_nested(a, group, nested, work, seen);
                    }
                    _ => {}
                }
            }
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                self.expr_collect_nested(t, group, nested, work, seen);
                self.expr_collect_nested(b, group, nested, work, seen);
            }
            ExprData::Let(t, v, b) => {
                self.expr_collect_nested(t, group, nested, work, seen);
                self.expr_collect_nested(v, group, nested, work, seen);
                self.expr_collect_nested(b, group, nested, work, seen);
            }
            ExprData::Proj(_, _, v) => self.expr_collect_nested(v, group, nested, work, seen),
            ExprData::Const(n, us) => {
                self.note_nested_induct(*n, us, &[], group, nested, work, seen)
            }
            _ => {}
        }
    }

    /// Record `F` when the spine is `F … I …` with `I` in `group`, then
    /// instantiate `F`'s constructors (`Array Syntax` yields `List Syntax`).
    fn note_nested_induct(
        &self,
        n: u32,
        us: &[Level],
        args: &[Expr],
        group: &[u32],
        nested: &mut Vec<u32>,
        work: &mut Vec<Expr>,
        seen: &mut Vec<u32>,
    ) {
        if group.contains(&n) {
            return;
        }
        let Some(ConstantInfo::InductiveType {
            num_params, all, ..
        }) = self.env.get(n)
        else {
            return;
        };
        let num_params = *num_params;
        if (args.len() as u32) < num_params {
            return;
        }
        let params = &args[..num_params as usize];
        if !params.iter().any(|a| self.occurs_any(a, group)) {
            return;
        }
        let all = all.clone();
        for m in all {
            if !nested.contains(&m) {
                nested.push(m);
            }
            if seen.contains(&m) {
                continue;
            }
            seen.push(m);
            let (ctors, m_params, subst) = match self.env.get(m) {
                Some(ConstantInfo::InductiveType {
                    ctors,
                    num_params: m_params,
                    level_params,
                    ..
                }) => (ctors.clone(), *m_params, level::subst_map(level_params, us)),
                _ => continue,
            };
            for c in ctors {
                if let Some(ConstantInfo::Constructor { typ, .. }) = self.env.get(c) {
                    let ty = expr::instantiate_level_params(typ, &subst);
                    work.extend(Self::ctor_field_tys(&ty, m_params, Some(params)));
                }
            }
        }
    }

    /// `tname` occurs as nested `F … I …` in a constructor field of the
    /// recursor group (`I` in `rec.all`). `Array Syntax` and `List Syntax`
    /// both count; `List Preresolved` does not.
    fn nested_type_in_group(&self, rname: u32, tname: u32) -> bool {
        let group = match self.env.get(rname) {
            Some(ConstantInfo::Recursor { all, .. }) => all.clone(),
            _ => return false,
        };
        if group.contains(&tname) {
            return false;
        }
        let mut scan = group.clone();
        for t in self.rec_group_all(rname) {
            if !scan.contains(&t) {
                scan.push(t);
            }
        }
        let mut nested = Vec::new();
        let mut work: Vec<Expr> = Vec::new();
        let mut seen: Vec<u32> = Vec::new();
        for t in &scan {
            let (ctors, nparams) = match self.env.get(*t) {
                Some(ConstantInfo::InductiveType {
                    ctors, num_params, ..
                }) => (ctors.clone(), *num_params),
                _ => continue,
            };
            for c in ctors {
                if let Some(ConstantInfo::Constructor { typ, .. }) = self.env.get(c) {
                    work.extend(Self::ctor_field_tys(typ, nparams, None));
                }
            }
        }
        let mut i = 0;
        while i < work.len() {
            let e = work[i].clone();
            self.expr_collect_nested(&e, &group, &mut nested, &mut work, &mut seen);
            i += 1;
        }
        nested.contains(&tname)
    }

    /// Owner: `cname.induct` is in `rec.all`, or a nested inductive in a
    /// group constructor field. Not “listed in `rules`”. `Syntax.rec_2` owns
    /// `List.nil`.
    fn rec_owns_ctor(&self, rname: u32, cname: u32) -> bool {
        let induct = match self.env.get(cname) {
            Some(ConstantInfo::Constructor { induct, .. }) => *induct,
            _ => return false,
        };
        let Some(ConstantInfo::Recursor { all, .. }) = self.env.get(rname) else {
            return false;
        };
        all.contains(&induct) || self.nested_type_in_group(rname, induct)
    }

    fn ctor_num_fields(&self, cname: u32) -> Option<u32> {
        match self.env.get(cname) {
            Some(ConstantInfo::Constructor { num_fields, .. }) => Some(*num_fields),
            _ => None,
        }
    }

    /// No ι when a rule for `cname` has `nfields` ≠ constructor `num_fields`.
    fn rule_nfields_agrees(&self, rname: u32, cname: u32, num_fields: u32) -> bool {
        let Some(ConstantInfo::Recursor { rules, .. }) = self.env.get(rname) else {
            return true;
        };
        match rules.iter().find(|r| r.ctor == cname) {
            Some(rule) => rule.nfields == num_fields,
            None => true,
        }
    }

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

        if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
            eprintln!(
                "IOTA rec={} major={} mhead={}",
                self.name_str(rname),
                self.pp_budget(major, 8),
                self.pp_budget(&mhead, 6)
            );
        }
        let ctor = match &**mhead {
            ExprData::Const(cname, _) => match self.env.get(*cname) {
                Some(ConstantInfo::Constructor {
                    num_params: cnp, ..
                }) if self.rec_owns_ctor(rname, *cname) => Some((*cname, *cnp, margs.clone())),
                _ => None,
            },
            ExprData::Lit(Lit::Nat(n)) => {
                if let Some((zero, succ)) = self.nat_ctors() {
                    if self.rec_owns_ctor(rname, zero) {
                        if n == &num_bigint::BigUint::from(0u32) {
                            Some((zero, 0, vec![]))
                        } else if n.bits() > 256 {
                            // Lean `LEAN_NAT_MAX_SIZE`-style byte cap, not a
                            // bits∈[20,24] fingerprint of hugeFuel vs 2^32.
                            return decline("Nat literal exceeds byte cap");
                        } else {
                            // One succ peel per iota (C++ natLit). WHNF-core
                            // may continue; uniform WHNF_DEPTH declines.
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
        } else if let Some(x) = self.to_ctor_when_structure(ctx, &all, params, &major_w)? {
            if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
                eprintln!(
                    "IOTA expand rec={} major={} → ctor {} nparams={} nfields={}",
                    self.name_str(rname),
                    self.pp_budget(&major_w, 8),
                    self.name_str(x.0),
                    x.1,
                    x.2.len()
                );
            }
            x
        } else if k_like {
            match self.k_like_ctor(ctx, &all, params, major)? {
                Some(x) => x,
                None => return Ok(None),
            }
        } else {
            return Ok(None);
        };

        if !self.rec_owns_ctor(rname, cname) {
            return Ok(None);
        }
        if (ctor_args.len() as u32) < cnp {
            return Ok(None);
        }
        let ctor_params = &ctor_args[..cnp as usize];
        let fields = &ctor_args[cnp as usize..];
        let Some(nfields) = self.ctor_num_fields(cname) else {
            return Ok(None);
        };
        if fields.len() as u32 != nfields || !self.rule_nfields_agrees(rname, cname, nfields) {
            return Ok(None);
        }

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

    /// K-like from the inductive: not mutual, one ctor, result Prop, zero
    /// fields. `num_params` / `num_indices` are the inductive's, never the
    /// recursor export. Exported `k` unused. Eq stays K-like (1 index).
    fn is_k_like(&self, all: &[u32]) -> R<bool> {
        if all.len() != 1 {
            return Ok(false);
        }
        self.is_k_like_ind(all[0])
    }

    fn is_k_like_ind(&self, tname: u32) -> R<bool> {
        let (ctors, num_params, num_indices, typ) = match self.env.get(tname) {
            Some(ConstantInfo::InductiveType {
                ctors,
                num_params,
                num_indices,
                typ,
                ..
            }) => (ctors.clone(), *num_params, *num_indices, typ.clone()),
            _ => return Ok(false),
        };
        if ctors.len() != 1 {
            return Ok(false);
        }
        let mut ctx: Ctx = Ctx::new();
        let mut cur = typ;
        for _ in 0..(num_params + num_indices) {
            match self.ensure_pi(&ctx, &cur) {
                Ok((_, dom, body)) => {
                    ctx.push(dom);
                    cur = body;
                }
                Err(e) => return decline_or_false(e),
            }
        }
        let w = match self.whnf(&ctx, &cur) {
            Ok(w) => w,
            Err(e) => return decline_or_false(e),
        };
        if matches!(&**w, ExprData::Pi(_, _, _)) {
            return Ok(false);
        }
        let lvl = match self.ensure_sort(&ctx, &w) {
            Ok(l) => l,
            Err(e) => return decline_or_false(e),
        };
        if !level::is_def_eq(&lvl, &level::zero()) {
            return Ok(false);
        }
        let (ctor_typ, ctor_nfields) = match self.env.get(ctors[0]) {
            Some(ConstantInfo::Constructor {
                typ, num_fields, ..
            }) => (typ.clone(), *num_fields),
            _ => return Ok(false),
        };
        if ctor_nfields != 0 {
            return Ok(false);
        }
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
                    if !self.rec_owns_ctor(rname, rule.ctor) {
                        continue;
                    }
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
                Err(e @ TcError::Decline(_)) => return Err(e),
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
        // Recursive-field classification is part of inductive/recursor
        // semantics, so it uses the same full-definition transparency as the
        // positivity checker. A reducibility hint on an ordinary `Def` must
        // not erase a recursive occurrence (tutorial/053, /121, /122).
        let mut ty = match self.positivity_whnf(ctx, field_ty) {
            Ok(ty) => ty,
            Err(e @ TcError::Decline(_)) => return Err(e),
            Err(_) => field_ty.clone(),
        };
        if std::env::var_os("KIOTA_TRACE_IOTA").is_some() {
            eprintln!(
                "REC-CALL field={} field_ty={} whnf={} params={}",
                self.pp_budget(field, 20),
                self.pp_budget(field_ty, 30),
                self.pp_budget(&ty, 30),
                params
                    .iter()
                    .map(|p| self.pp_budget(p, 10))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        let mut binders: Vec<Expr> = Vec::new();
        let mut tctx = ctx.clone();
        loop {
            match &**ty {
                ExprData::Pi(_, dom, body) => {
                    binders.push(dom.clone());
                    tctx.push(dom.clone());
                    ty = match self.positivity_whnf(&tctx, body) {
                        Ok(ty) => ty,
                        Err(e @ TcError::Decline(_)) => return Err(e),
                        Err(_) => body.clone(),
                    };
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
            (
                rec,
                iargs[..nparams].to_vec(),
                &iargs[nparams..],
            )
        } else if self.occurs_any(&ty, all) {
            // Only `F … I …` (e.g. `Array Syntax`), not `List Preresolved`.
            if let Some(nrec) = self.nested_rec_for(target, rname) {
                (nrec, params.iter().map(|p| expr::shift(p, shift_by, 0)).collect(), &[][..])
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
        // Binder types were captured while walking the telescope: binders[0]
        // at the original depth, binders[k] under the previous k binders
        // (so the immediately-outer variable is already `#0`). Wrapping
        // inside-out must not shift by `i` — that turned Acc.intro's
        // `∀ y, r y x → Acc r y` into `λ y. λ h : r #1 x. …` (`y` as `#1`
        // instead of `#0`), and `WellFounded.fixF_eq` then failed to convert
        // the iota rec-call with `fun y p => fixF F y (Acc.inv … p)`.
        for bty in binders.iter().rev() {
            rec_app = expr::lam(crate::expr::BinderInfo::Default, bty.clone(), rec_app);
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
                    let large_lit = |e: &Expr| {
                        nat::as_lit(e).is_some_and(|n| n.bits() >= 16)
                    };
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
            "HAdd.hAdd" | "Add.add" | "HMul.hMul" | "Mul.mul" | "HPow.hPow" | "Pow.pow"
            | "HSub.hSub" | "Sub.sub" | "HMod.hMod" | "Mod.mod" | "HDiv.hDiv" | "Div.div"
            | "HShiftLeft.hShiftLeft" | "ShiftLeft.shiftLeft" | "HShiftRight.hShiftRight" | "ShiftRight.shiftRight"
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
            "Decidable.decide" | "decide" if args.len() >= 2 => {
                let inst = self.whnf(ctx, &args[1])?;
                let (ih, iargs) = expr::unfold_apps(&inst);
                let iname = match &**ih {
                    ExprData::Const(n, _) => self.name_str(*n),
                    _ => return Ok(None),
                };
                let tname = if iname == "Decidable.isTrue" {
                    "Bool.true"
                } else if iname == "Decidable.isFalse" {
                    "Bool.false"
                } else if (iname == "Int.decLe" || iname == "Int.decLt") && iargs.len() >= 2 {
                    let aw = self.whnf(ctx, &iargs[0])?;
                    let bw = self.whnf(ctx, &iargs[1])?;
                    let (Some(a), Some(b)) = (
                        self.closed_int_value(ctx, &aw)?,
                        self.closed_int_value(ctx, &bw)?,
                    ) else {
                        return Ok(None);
                    };
                    let yes = if iname == "Int.decLt" { a < b } else { a <= b };
                    if yes {
                        "Bool.true"
                    } else {
                        "Bool.false"
                    }
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
                if ty_name == "Int" {
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
                if ty_name != "Int" {
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
                if ty_name == "Int" {
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
                if ty_name == "Int" {
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
            "HAdd.hAdd" | "HMul.hMul" | "HPow.hPow" | "HSub.hSub" | "HMod.hMod" | "HDiv.hDiv"
            | "HShiftLeft.hShiftLeft" | "HShiftRight.hShiftRight" => (0usize, 4usize, 6usize),
            "Add.add" | "Mul.mul" | "Pow.pow" | "Sub.sub" | "Mod.mod" | "Div.div"
            | "ShiftLeft.shiftLeft" | "ShiftRight.shiftRight" => (0usize, 2usize, 4usize),
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
    /// cannot unfold `modCore.go` before the instance constructor is seen.
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
        let is_inv = ident == "inv" && is_rat_ident(name, ident);
        let is_num = ident == "num" && is_rat_ident(name, ident);
        let is_den = ident == "den" && is_rat_ident(name, ident);
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

    fn rat_closed_parts(
        &self,
        ctx: &Ctx,
        e: &Expr,
    ) -> R<Option<(BigInt, BigUint, Expr)>> {
        let e = self.whnf(ctx, e)?;
        let (h, args) = expr::unfold_apps(&e);
        let name = match &**h {
            ExprData::Const(n, _) => self.name_str(*n),
            _ => return Ok(None),
        };
        let ident = name.rsplit('.').next().unwrap_or(name);
        if ident == "mk'" && is_rat_ident(name, ident) && args.len() >= 4 {
            let Some(num) = self.closed_int_value(ctx, &args[args.len() - 4])? else {
                return Ok(None);
            };
            let Some(den) = self.closed_nat_value(ctx, &args[args.len() - 3])? else {
                return Ok(None);
            };
            return Ok(Some((num, den, e)));
        }
        if ident == "ofInt" && is_rat_ident(name, ident) && !args.is_empty() {
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
            let r = LinearPoly::combine_mul_k(
                &BigInt::from(1),
                &BigInt::from(1),
                &p1,
                &p2,
            );
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
                        eprintln!("LINEAR diseq: p1 parse fail {}", self.pp_budget(&args[1], 40));
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
                        eprintln!("LINEAR diseq: p3 parse fail {}", self.pp_budget(&args[3], 40));
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
                Some(LinearExpr::Sub(Box::new(lhs), Box::new(rhs)).norm().beq(&want))
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
                let want = LinearPoly::Add(
                    BigInt::from(1),
                    x,
                    Box::new(LinearPoly::Num(-k)),
                );
                Some(LinearExpr::Sub(Box::new(lhs), Box::new(rhs)).norm().beq(&want))
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
                let want = LinearPoly::Add(
                    BigInt::from(1),
                    x,
                    Box::new(LinearPoly::Num(-k)),
                );
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
            let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[args.len() - 2])?)? else {
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
            let Some(k) = self.closed_int_value(ctx, &self.whnf(ctx, &args[args.len() - 1])?)? else {
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
        let ident = name.rsplit('.').next().unwrap_or(name);
        if !is_commring_ident(name, ident) {
            return Ok(None);
        }
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
            if self.is_closed_int_list(&a) && self.is_closed_int_list(&b) && self.is_list_nil(&b)
            {
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
            if let Some(r) = self.closed_coeffs_combo(
                ctx, &args[0], &args[1], &args[2], &args[3],
            )? {
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
    fn omega_tidy(
        &self,
        ctx: &Ctx,
        s: &Expr,
        x: &Expr,
    ) -> R<Option<(Expr, Expr)>> {
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

    fn closed_option_int(
        &self,
        ctx: &Ctx,
        e: &Expr,
    ) -> R<Option<Option<num_bigint::BigInt>>> {
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
            return !args.is_empty()
                && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
        }
        if name == "Int.negSucc" || name.ends_with(".Int.negSucc") {
            return !args.is_empty()
                && matches!(&**args[0], ExprData::Lit(Lit::Nat(_)));
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
    fn type_head_is_int(&self, e: &Expr) -> bool {
        let (h, _) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) => self.name_str(*n) == "Int",
            _ => false,
        }
    }

    fn closed_int_value(&self, ctx: &Ctx, e: &Expr) -> R<Option<BigInt>> {
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
            if !self.type_head_is_int(&args[0]) {
                return Ok(None);
            }
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
        if (name == "Int.add" || name.ends_with(".Int.add") || name == "Int.sub" || name.ends_with(".Int.sub")
            || name == "Int.mul" || name.ends_with(".Int.mul"))
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
        if (name == "HAdd.hAdd" || name == "HSub.hSub" || name == "HMul.hMul") && args.len() >= 6
        {
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
        Some(expr::app(
            expr::const_(ns, vec![]),
            nat::mk_lit(mag - 1u32),
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
            let (cnst, coeffs) =
                if (lname == "LinearCombo.mk" || lname.ends_with(".LinearCombo.mk"))
                    && largs.len() >= 2
                {
                    (largs[0].clone(), largs[1].clone())
                } else {
                    (
                        expr::proj(combo, 0, lc.clone()),
                        expr::proj(combo, 1, lc),
                    )
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

    /// Is `sname` Lean's native `String`, in the exact shape whose literal
    /// representation the kernel may assume?
    ///
    /// Reducing `Proj(String, 0, "abc")` to `ByteArray.mk (Array.mk UInt8 …)`
    /// asserts a representation the export never wrote down. That is only
    /// justified if the declared `String` really is Lean's: a non-unsafe,
    /// parameterless, index-free `Sort 1` inductive named `String`, alone in
    /// its mutual group, with exactly one constructor taking exactly one
    /// first field of type `ByteArray`. A name check alone is forgeable — an export
    /// can declare its own `String` with a different field and inherit the
    /// native semantics.
    fn authenticated_native_string(&self, sname: u32) -> bool {
        let Some(ConstantInfo::InductiveType {
            level_params,
            typ,
            num_params: 0,
            num_indices: 0,
            all,
            ctors,
            is_unsafe: false,
            ..
        }) = self.env.get(sname)
        else {
            return false;
        };
        if self.name_str(sname) != "String"
            || !level_params.is_empty()
            || **typ != *expr::sort(level::succ(level::zero()))
            || all.as_slice() != [sname]
            || ctors.len() != 1
        {
            return false;
        }
        let Some(ConstantInfo::Constructor {
            typ: ctyp,
            num_params: 0,
            num_fields,
            level_params: clp,
            ..
        }) = self.env.get(ctors[0])
        else {
            return false;
        };
        // Lean's String is `String.ofByteArray (data : ByteArray) (valid : …)`
        // — two fields, the second a validity proof. Only field 0 determines
        // the representation this reduction produces, so require field 0 to
        // be the ByteArray and leave the rest to ordinary checking.
        if !clp.is_empty() || *num_fields < 1 {
            return false;
        }
        let ExprData::Pi(_, dom, _) = &***ctyp else {
            return false;
        };
        matches!(&***dom, ExprData::Const(b, us)
            if us.is_empty() && self.name_str(*b) == "ByteArray")
    }

    fn string_to_byte_array(&self, s: &str) -> Option<Expr> {
        let ba_mk = self.find_name("ByteArray.mk")?;
        let arr_mk = self.find_name("Array.mk")?;
        let uint8 = self.find_name("UInt8")?;
        let list_nil = self.find_name("List.nil")?;
        let list_cons = self.find_name("List.cons")?;
        let uint8_ty = expr::const_(uint8, vec![]);
        let mut list = expr::app(expr::const_(list_nil, vec![level::zero()]), uint8_ty.clone());
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
        // Kernel formation is a separate gate from the redundant metadata
        // checks below.  Check the complete inductive, constructor, and
        // recursor types so malformed binder domains or ill-typed conclusion
        // indices cannot hide behind a well-shaped telescope.
        for tname in &all {
            self.check_decl(*tname, "inductive type")?;
            if let Some(ConstantInfo::InductiveType { ctors, .. }) = self.env.get(*tname) {
                for cname in ctors {
                    self.check_decl(*cname, "constructor")?;
                }
            }
        }
        if let Some(main_rec) = self.env.rec_of.get(&first_name) {
            let recs = self
                .env
                .rec_group
                .get(main_rec)
                .cloned()
                .unwrap_or_else(|| vec![*main_rec]);
            for rname in recs {
                self.check_decl(rname, "recursor")?;
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
                            let field_lvl = self.ensure_sort(&c2, &ds)?;
                            if !level::is_geq(&t_sort, &field_lvl)
                                && !level::normalizes_to_zero(&t_sort)
                            {
                                return reject(
                                    "constructor field universe is too big for the inductive type",
                                );
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
        for tname in &all {
            if let Some(rname) = self.env.rec_of.get(tname) {
                self.check_main_recursor(*rname, *tname, &all)?;
            }
        }
        Ok(())
    }

    /// Authenticate a main recursor independently of exported rule RHS terms.
    /// Its result must be the appropriate motive applied to the declared
    /// indices and major premise, and reducing it on every constructor must
    /// preserve that result type.  This is the defensive `check_recursors`
    /// boundary used by Lean's kernel, adapted to de Bruijn contexts.
    fn check_main_recursor(&self, rname: u32, owner: u32, all: &[u32]) -> R<()> {
        let (r_lp, r_typ, num_params, num_indices, num_motives, num_minors) =
            match self.env.get(rname) {
                Some(ConstantInfo::Recursor {
                    level_params,
                    typ,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    ..
                }) => (
                    level_params.clone(),
                    typ.clone(),
                    *num_params,
                    *num_indices,
                    *num_motives,
                    *num_minors,
                ),
                _ => return reject("main recursor declaration is missing"),
            };
        let owner_pos = all
            .iter()
            .position(|n| *n == owner)
            .ok_or_else(|| TcError::Reject("recursor owner is outside its mutual group".into()))?;
        if owner_pos >= num_motives as usize {
            return reject("recursor has no motive for its owner");
        }
        let prefix = (num_params + num_motives + num_minors) as usize;

        // Check the final `indices -> major -> motive indices major` spine.
        let mut ctx = Ctx::new();
        let mut cur = r_typ.clone();
        for _ in 0..prefix {
            let (_, dom, body) = self.ensure_pi(&ctx, &cur)?;
            ctx.push(dom);
            cur = body;
        }
        for _ in 0..num_indices {
            let (_, dom, body) = self.ensure_pi(&ctx, &cur)?;
            ctx.push(dom);
            cur = body;
        }
        let (_, major_dom, result) = self.ensure_pi(&ctx, &cur)?;
        let (major_head, major_args) = expr::unfold_apps(&major_dom);
        if !matches!(&**major_head, ExprData::Const(n, _) if *n == owner)
            || major_args.len() != (num_params + num_indices) as usize
        {
            return reject("recursor major premise does not match its inductive owner");
        }
        for i in 0..num_params as usize {
            let expected = expr::bvar((ctx.len() - 1 - i) as u32);
            if !self.is_def_eq(&ctx, &major_args[i], &expected)? {
                return reject("recursor major premise uses the wrong parameter");
            }
        }
        for i in 0..num_indices as usize {
            let pos = prefix + i;
            let expected = expr::bvar((ctx.len() - 1 - pos) as u32);
            if !self.is_def_eq(&ctx, &major_args[num_params as usize + i], &expected)? {
                return reject("recursor major premise uses the wrong index");
            }
        }
        ctx.push(major_dom);
        let motive_pos = num_params as usize + owner_pos;
        let mut expected_result = expr::bvar((ctx.len() - 1 - motive_pos) as u32);
        for i in 0..num_indices as usize {
            let pos = prefix + i;
            expected_result = expr::app(
                expected_result,
                expr::bvar((ctx.len() - 1 - pos) as u32),
            );
        }
        expected_result = expr::app(expected_result, expr::bvar(0));
        if !self.is_def_eq(&ctx, &result, &expected_result)? {
            return reject("recursor result is not its motive applied to indices and major");
        }

        let ctors = match self.env.get(owner) {
            Some(ConstantInfo::InductiveType { ctors, .. }) => ctors.clone(),
            _ => return reject("recursor owner is not an inductive type"),
        };
        let r_levels: Vec<Level> = r_lp.iter().map(|p| level::param(*p)).collect();
        for cname in ctors {
            let (c_lp, c_typ) = match self.env.get(cname) {
                Some(ConstantInfo::Constructor {
                    level_params, typ, ..
                }) => (level_params.clone(), typ.clone()),
                _ => return reject("recursor owner lists a non-constructor"),
            };
            let mut cctx = Ctx::new();
            let mut rcur = r_typ.clone();
            for _ in 0..prefix {
                let (_, dom, body) = self.ensure_pi(&cctx, &rcur)?;
                cctx.push(dom);
                rcur = body;
            }
            let mut ccur = c_typ;
            for i in 0..num_params as usize {
                let (_, _, body) = self.ensure_pi(&cctx, &ccur)?;
                let param = expr::bvar((cctx.len() - 1 - i) as u32);
                ccur = expr::instantiate1(&body, &param);
            }
            let field_start = cctx.len();
            loop {
                match &**ccur {
                    ExprData::Pi(_, dom, body) => {
                        cctx.push(dom.clone());
                        ccur = body.clone();
                    }
                    _ => break,
                }
            }
            let (conclusion_head, conclusion_args) = expr::unfold_apps(&ccur);
            if !matches!(&**conclusion_head, ExprData::Const(n, _) if *n == owner)
                || conclusion_args.len() != (num_params + num_indices) as usize
            {
                return reject("constructor conclusion does not match recursor owner");
            }
            let mut lhs = expr::const_(rname, r_levels.clone());
            for pos in 0..prefix {
                lhs = expr::app(lhs, expr::bvar((cctx.len() - 1 - pos) as u32));
            }
            for index in &conclusion_args[num_params as usize..] {
                lhs = expr::app(lhs, index.clone());
            }
            let c_levels: Vec<Level> = c_lp.iter().map(|p| level::param(*p)).collect();
            let mut intro = expr::const_(cname, c_levels);
            for pos in 0..num_params as usize {
                intro = expr::app(intro, expr::bvar((cctx.len() - 1 - pos) as u32));
            }
            for pos in field_start..cctx.len() {
                intro = expr::app(intro, expr::bvar((cctx.len() - 1 - pos) as u32));
            }
            lhs = expr::app(lhs, intro);
            let expected = self.infer_type(&cctx, &lhs)?;
            let reduct = self.whnf(&cctx, &lhs)?;
            if Rc::ptr_eq(&reduct, &lhs) {
                return reject("recursor did not reduce on its constructor");
            }
            let actual = self.infer_type(&cctx, &reduct)?;
            if !self.is_def_eq(&cctx, &actual, &expected)? {
                if std::env::var_os("KIOTA_DEBUG").is_some() {
                    return reject(format!(
                        "recursor computation is not type-preserving\n  lhs:      {}\n  reduct:   {}\n  actual:   {}\n  expected: {}",
                        self.pp_budget(&lhs, 80),
                        self.pp_budget(&reduct, 80),
                        self.pp_budget(&actual, 80),
                        self.pp_budget(&expected, 80),
                    ));
                }
                return reject("recursor computation is not type-preserving");
            }
        }
        Ok(())
    }

    /// Walk a constructor's argument telescope; each argument type must be
    /// strictly positive in the names being defined (`bound`).
    fn check_positivity(&self, ctx: &Ctx, e: &Expr, bound: &[u32], _strict_pos_ok: bool) -> R<()> {
        let w = self.positivity_whnf(ctx, e)?;
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

    fn positivity_whnf(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        // Lean's inductive checker uses the kernel's full WHNF here.  Unlike
        // our hot-path WHNF heuristic, that unfolds every `Def`, including a
        // definition exported with the opaque reducibility *hint*.  (`Opaque`
        // declarations remain a distinct, irreducible kind.)
        let mut cur = e.clone();
        for _ in 0..CONV_DEPTH {
            let w = match self.whnf(ctx, &cur) {
                Ok(w) => w,
                Err(TcError::Decline(m)) => return Err(TcError::Decline(m)),
                Err(_) => return reject("cannot prove constructor argument is positive"),
            };
            match self.try_unfold_const_head(&w) {
                Ok(Some(next)) if !Rc::ptr_eq(&next, &w) => {
                    cur = next;
                }
                Ok(_) => return Ok(w),
                Err(TcError::Decline(m)) => return Err(TcError::Decline(m)),
                Err(_) => return reject("cannot prove constructor argument is positive"),
            }
        }
        decline("positivity WHNF depth limit")
    }

    /// Strict positivity: `bound` may not occur in a Pi domain. Direct
    /// `I params..` is allowed. Nested `F … I …` is allowed when `F` is a
    /// previously defined inductive whose constructors are strictly positive
    /// in `I`.
    fn check_arg_positive(
        &self,
        ctx: &Ctx,
        arg_ty: &Expr,
        bound: &[u32],
        num_params: u32,
    ) -> R<()> {
        self.check_arg_positive_in(ctx, arg_ty, bound, num_params, &[])
    }

    fn check_arg_positive_in(
        &self,
        ctx: &Ctx,
        arg_ty: &Expr,
        bound: &[u32],
        num_params: u32,
        visiting: &[(u32, Vec<Expr>)],
    ) -> R<()> {
        let mut cur = self.positivity_whnf(ctx, arg_ty)?;
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
                    cur = self.positivity_whnf(&ctx2, body)?;
                }
                _ => break,
            }
        }
        self.check_positive_spine(&ctx2, &cur, bound, num_params, visiting)
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
            if !self.is_def_eq(ctx, a, e)? {
                return reject("non-uniform nested inductive parameter");
            }
        }
        Ok(())
    }

    fn params_defeq(&self, ctx: &Ctx, a: &[Expr], b: &[Expr]) -> R<bool> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (x, y) in a.iter().zip(b.iter()) {
            if !self.is_def_eq(ctx, x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_positive_spine(
        &self,
        ctx: &Ctx,
        e: &Expr,
        bound: &[u32],
        num_params: u32,
        visiting: &[(u32, Vec<Expr>)],
    ) -> R<()> {
        if !self.occurs_any(e, bound) {
            return Ok(());
        }
        let (h, args) = expr::unfold_apps(e);
        match &**h {
            ExprData::Const(n, _) if bound.contains(n) => {
                self.check_uniform_i(ctx, &args, bound, num_params)
            }
            ExprData::Const(n, us) => match self.env.get(*n) {
                Some(ConstantInfo::InductiveType { .. }) => {
                    self.check_nested_functor(ctx, *n, us, &args, bound, num_params, visiting)
                }
                _ => reject("occurrence of inductive type in unsupported position"),
            },
            _ => reject("occurrence of inductive type in unsupported position"),
        }
    }

    /// Lean eliminates `F Ds` to an auxiliary mutual type, then positivity
    /// is checked on the specialized constructors. Export form still has
    /// `F Ds`, so instantiate F's constructors at `Ds` and require those
    /// fields to be strictly positive in `bound`.
    /// Nested positivity recurses through instantiated constructor fields,
    /// which strictly grows the term, so the `visiting` cycle check (a
    /// structural compare of the argument vector) never matches and the
    /// mutual recursion with `check_arg_positive_in` does not terminate —
    /// cedar spun here indefinitely. Bound the nesting depth. Positivity is a
    /// soundness check, so exceeding the bound must not accept: Decline says
    /// "not verified" rather than claiming the type is positive.
    fn check_nested_functor(
        &self,
        ctx: &Ctx,
        f_name: u32,
        f_us: &[Level],
        args: &[Expr],
        bound: &[u32],
        i_num_params: u32,
        visiting: &[(u32, Vec<Expr>)],
    ) -> R<()> {
        if visiting.len() >= NESTED_POSITIVITY_DEPTH {
            return decline("nested positivity nesting too deep to verify");
        }
        let (f_np, f_all, f_lp) = match self.env.get(f_name) {
            Some(ConstantInfo::InductiveType {
                num_params,
                all,
                level_params,
                ..
            }) => (*num_params, all.clone(), level_params.clone()),
            _ => return reject("occurrence of inductive type in unsupported position"),
        };
        if args.len() < f_np as usize {
            return reject("nested inductive applied to too few parameters");
        }
        if f_lp.len() != f_us.len() {
            return reject("nested inductive universe mismatch");
        }
        let param_args = &args[..f_np as usize];
        let index_args = &args[f_np as usize..];
        for (n, ps) in visiting {
            if *n == f_name && self.params_defeq(ctx, ps, param_args)? {
                for ix in index_args {
                    if self.occurs_any(ix, bound) {
                        return reject("nested inductive occurrence in an index");
                    }
                }
                return Ok(());
            }
        }
        if !param_args.iter().any(|a| self.occurs_any(a, bound)) {
            return reject("occurrence of inductive type in unsupported position");
        }
        for ix in index_args {
            if self.occurs_any(ix, bound) {
                return reject("nested inductive occurrence in an index");
            }
        }
        let group: Vec<u32> = if f_all.is_empty() {
            vec![f_name]
        } else {
            f_all
        };
        let mut visiting2 = visiting.to_vec();
        for tname in &group {
            visiting2.push((*tname, param_args.to_vec()));
        }
        for tname in &group {
            let ctors = match self.env.get(*tname) {
                Some(ConstantInfo::InductiveType { ctors, .. }) => ctors.clone(),
                _ => continue,
            };
            for cname in &ctors {
                self.check_specialized_ctor_positive(
                    ctx,
                    *cname,
                    f_us,
                    param_args,
                    bound,
                    i_num_params,
                    &visiting2,
                )?;
            }
        }
        Ok(())
    }

    fn check_specialized_ctor_positive(
        &self,
        ctx: &Ctx,
        cname: u32,
        f_us: &[Level],
        param_args: &[Expr],
        bound: &[u32],
        i_num_params: u32,
        visiting: &[(u32, Vec<Expr>)],
    ) -> R<()> {
        let (lp, typ, c_np) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                num_params,
                ..
            }) => (level_params.clone(), typ.clone(), *num_params),
            _ => return reject("nested inductive constructor is missing"),
        };
        if c_np as usize != param_args.len() {
            return reject("nested inductive constructor numParams mismatch");
        }
        if lp.len() != f_us.len() {
            return reject("nested inductive constructor universe mismatch");
        }
        let subst = level::subst_map(&lp, f_us);
        let mut cur = expr::instantiate_level_params(&typ, &subst);
        for a in param_args {
            match &**cur {
                ExprData::Pi(_, _, body) => {
                    cur = expr::instantiate1(body, a);
                }
                _ => {
                    return reject(
                        "nested inductive constructor is not a function of its parameters",
                    )
                }
            }
        }
        let mut ctx2 = {
            crate::stats::ctx_clone();
            ctx.clone()
        };
        loop {
            match &**cur {
                ExprData::Pi(_, dom, body) => {
                    self.check_arg_positive_in(&ctx2, dom, bound, i_num_params, visiting)?;
                    ctx2.push(dom.clone());
                    cur = body.clone();
                }
                _ => break,
            }
        }
        let (h, cargs) = expr::unfold_apps(&cur);
        if let ExprData::Const(n, _) = &**h {
            if let Some(ConstantInfo::InductiveType { num_params: np, .. }) = self.env.get(*n) {
                for ix in cargs.get(*np as usize..).unwrap_or(&[]) {
                    if self.occurs_any(ix, bound) {
                        return reject("nested inductive occurrence in an index");
                    }
                }
                return Ok(());
            }
        }
        if self.occurs_any(&cur, bound) {
            return reject("occurrence of inductive type in unsupported position");
        }
        Ok(())
    }

    fn occurs_any(&self, e: &Expr, names: &[u32]) -> bool {
        // Interned exprs are a DAG. A naive recursive walk re-visits every
        // shared subterm once per path into it, which is exponential in the
        // sharing depth — perf/app-lam's `dag_app_binder` never finished.
        // Visit each node once by pointer identity instead.
        let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut stack: Vec<Expr> = vec![e.clone()];
        while let Some(cur) = stack.pop() {
            if !seen.insert(Rc::as_ptr(&cur) as usize) {
                continue;
            }
            match &**cur {
                ExprData::Const(n, _) => {
                    if names.contains(n) {
                        return true;
                    }
                }
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
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantInfo, Environment};
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
    fn suffix_ctx_key_uses_innermost_k_binders() {
        let a = ctx_of(&[1, 2, 3]);
        let b = ctx_of(&[9, 2, 3]);
        assert_ne!(a.id, b.id, "full telescopes differ at the outer binder");
        let e = expr::bvar(0);
        assert_eq!(
            a.term_ctx_key(&e),
            b.term_ctx_key(&e),
            "loose=1 keys on the innermost binder only"
        );
        let e1 = expr::app(expr::bvar(1), expr::bvar(0));
        assert_eq!(
            a.term_ctx_key(&e1),
            b.term_ctx_key(&e1),
            "loose=2 keys on the two innermost binders"
        );
        let e2 = expr::bvar(2);
        assert_ne!(
            a.term_ctx_key(&e2),
            b.term_ctx_key(&e2),
            "loose=3 sees the outer binder"
        );
        assert_eq!(a.term_ctx_key(&ty(0)), 0, "closed terms keep ctx_key 0");
    }

    /// `#18041` AIG `BinaryInput.mk` only mentions `aig`/`input` (high bvars).
    /// Extra innermost binders from `Decidable.rec` must not split the defeq
    /// pair cache — that walked intern-distinct copies as a tree.
    #[test]
    fn ctx_key_uses_actual_bvar_types_not_unused_inner() {
        let a = ctx_of(&[1, 2, 3]);
        let b = ctx_of(&[1, 9, 3]);
        assert_ne!(a.id, b.id, "middle binder differs");
        let e = expr::bvar(2);
        assert_eq!(
            a.term_ctx_key(&e),
            b.term_ctx_key(&e),
            "bvar 2 keys on that binder's type only, not unused inner binders"
        );
        let mk = expr::app(expr::app(ty(5), expr::bvar(2)), expr::bvar(2));
        assert_eq!(
            a.pair_ctx_key(&mk, &mk),
            b.pair_ctx_key(&mk, &mk),
            "structure-ctor apps that only mention bvar 2 share a pair key"
        );
        assert_ne!(
            a.term_ctx_key(&expr::bvar(1)),
            b.term_ctx_key(&expr::bvar(1)),
            "a term that uses the middle binder still sees the difference"
        );
    }

    /// Open binder types (`Vec #0`) still share a suffix key. Falling back to
    /// the full `ctx.id` re-Checks a 34k-DAG well-founded proof once per extra
    /// PSigma/Acc motive (`._unary` / `blastAdd.go_denote_eq`).
    #[test]
    fn suffix_ctx_key_shares_open_innermost_binder() {
        let vec0 = expr::app(ty(99), expr::bvar(0));
        assert!(expr::loose_bvar_range(&vec0) > 0);
        let mut a = Ctx::new();
        a.push(ty(1));
        a.push(vec0.clone());
        let mut b = Ctx::new();
        b.push(ty(2));
        b.push(vec0);
        let e = expr::bvar(0);
        assert_eq!(
            a.term_ctx_key(&e),
            b.term_ctx_key(&e),
            "loose=1 keys on the raw innermost type, even when that type mentions the parent"
        );
        assert_ne!(a.id, b.id);
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

    fn nest_apps(base: Expr, n: u32) -> Expr {
        let mut e = base.clone();
        for _ in 0..n {
            e = expr::app(e, base.clone());
        }
        e
    }

    /// Shared spine, exponential tree size, intern depth = `depth`.
    fn bush(base: Expr, depth: u32) -> Expr {
        let mut e = base;
        for _ in 0..depth {
            e = expr::app(e.clone(), e.clone());
        }
        e
    }

    /// Eager WHNF unfolds every non-opaque Def (`has_value`). Size/name
    /// are not skip gates. Names are unrelated to AIG / LawfulOperator.
    #[test]
    fn large_regular_def_unfolds_in_whnf() {
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
                value: large_body.clone(),
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let medium = bush(dummy.clone(), 12);
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
        let big = bush(dummy.clone(), 14);
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
            "abbrev still unfolds in WHNF"
        );
        let w_large = tc.whnf(&ctx, &expr::const_(2, vec![])).unwrap();
        assert!(
            Rc::ptr_eq(&w_large, &large_body),
            "large Regular unfolds in WHNF (has_value); size is not a skip"
        );
    }

    /// Related-def / Eq-head tables are not a WHNF gate. A Regular ≥ 4096
    /// unfolds in WHNF (`is_delta` = has_value) with empty tables.
    #[test]
    fn large_regular_converts_without_eq_head_table() {
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
        let body = bush(dummy.clone(), 13);
        assert!(
            expr_size_capped(&body, 10_000) >= 4_096,
            "body must exceed the WHNF Regular size band"
        );
        env.insert(
            1,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort0,
                value: body.clone(),
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let names = test_names(&["Dummy", "bigReg"]);
        let tc = Checker::new(&env, &names, None, None);
        assert!(
            tc.eq_arg_heads.borrow().is_empty() && tc.eq_related_defs.borrow().is_empty(),
            "no theorem Eq-head table on a fresh checker"
        );
        assert!(
            tc.eager_whnf_unfolds(1),
            "has_value Regular unfolds regardless of Eq-head tables"
        );
        assert!(
            tc.is_delta_reducible(1),
            "lazy delta still has_value for the large Regular"
        );
        let eq = tc
            .is_def_eq(&Ctx::new(), &expr::const_(1, vec![]), &body)
            .unwrap_or(false);
        assert!(eq, "large Regular converts without related-def / Eq-heads");
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

    /// `exfalso junk` with a ≥10k-node junk term of type True. Lean
    /// `check`s the theorem value; infer_only on the whole value would accept it.
    #[test]
    fn large_theorem_still_checks_app_args() {
        use crate::env::{ConstantInfo, Environment};
        let sort0 = expr::sort(level::zero());
        let mut env = Environment::default();
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
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort0.clone(),
                is_unsafe: false,
            },
        );
        let false_ty = expr::const_(0, vec![]);
        let true_ty = expr::const_(1, vec![]);
        env.insert(
            2,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, false_ty, true_ty.clone()),
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    true_ty.clone(),
                    expr::pi(expr::BinderInfo::Default, true_ty.clone(), true_ty.clone()),
                ),
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: true_ty.clone(),
                is_unsafe: false,
            },
        );
        let and_t = expr::const_(3, vec![]);
        let mut junk = expr::const_(4, vec![]);
        for _ in 0..16 {
            junk = expr::app(expr::app(and_t.clone(), junk.clone()), junk);
        }
        assert!(
            expr_size_capped(&junk, 20_000) >= 10_000,
            "junk must trip the old ≥10k infer_only gate"
        );
        env.insert(
            5,
            ConstantInfo::Theorem {
                level_params: vec![],
                typ: true_ty,
                value: expr::app(expr::const_(2, vec![]), junk),
            },
        );
        let names = [
            std::rc::Rc::new("False".into()),
            std::rc::Rc::new("True".into()),
            std::rc::Rc::new("exfalso".into()),
            std::rc::Rc::new("andT".into()),
            std::rc::Rc::new("intro".into()),
            std::rc::Rc::new("bad".into()),
        ];
        let tc = Checker::new(&env, &names, None, None);
        match tc.check_decl(5, "theorem") {
            Err(TcError::Reject(msg)) => assert!(
                msg.contains("application argument type mismatch"),
                "expected app-arg reject, got {msg}"
            ),
            other => panic!("large ill-typed theorem must reject, got {other:?}"),
        }
    }

    fn test_names(ss: &[&str]) -> Vec<std::rc::Rc<String>> {
        ss.iter().map(|s| std::rc::Rc::new((*s).into())).collect()
    }

    fn axiom_sort(env: &mut Environment, name: u32, typ: Expr) {
        env.insert(
            name,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ,
                is_unsafe: false,
            },
        );
    }

    /// `False` / `True` as inductives (not axioms). `True.intro` is a ctor.
    fn insert_false_true(env: &mut Environment) {
        let sort0 = expr::sort(level::zero());
        env.insert(
            0,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort0.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![0],
                ctors: vec![],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort0.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![1],
                ctors: vec![2],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: expr::const_(1, vec![]),
                induct: 1,
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            },
        );
    }

    fn assert_app_mismatch(r: R<()>) {
        match r {
            Err(TcError::Reject(msg)) => assert!(
                msg.contains("application argument type mismatch"),
                "expected app-arg reject, got {msg}"
            ),
            other => panic!("ill-typed theorem must reject, got {other:?}"),
        }
    }

    /// `idT (False.elim True.intro)` with True/False inductives. InferOnly on
    /// the Prop binder of `idT` currently skips Check of the inner app.
    #[test]
    fn idt_false_elim_true_intro_rejects() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let false_ty = expr::const_(0, vec![]);
        let true_ty = expr::const_(1, vec![]);
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, false_ty, true_ty.clone()),
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    true_ty.clone(),
                    true_ty.clone(),
                ),
                value: expr::lam(expr::BinderInfo::Default, true_ty.clone(), expr::bvar(0)),
                hints: crate::env::ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let junk = expr::app(expr::const_(3, vec![]), expr::const_(2, vec![]));
        env.insert(
            5,
            ConstantInfo::Theorem {
                level_params: vec![],
                typ: true_ty,
                value: expr::app(expr::const_(4, vec![]), junk),
            },
        );
        let names = test_names(&["False", "True", "True.intro", "elim", "idT", "bad"]);
        let tc = Checker::new(&env, &names, None, None);
        assert_app_mismatch(tc.check_decl(5, "theorem"));
    }

    /// `Prop` is a universe, not a proposition. PI must not make `True ≡ False`.
    #[test]
    fn true_and_false_are_not_proof_irrelevant() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let names = test_names(&["False", "True", "True.intro"]);
        let tc = Checker::new(&env, &names, None, None);
        let eq = tc
            .is_def_eq(&Ctx::new(), &expr::const_(1, vec![]), &expr::const_(0, vec![]))
            .expect("defeq");
        assert!(!eq, "True and False must not convert by PI of Prop");
    }

    /// Two `Cl.mk` spines with PI-equal but not pointer-equal `True` fields
    /// must convert by proof irrelevance, not by walking 7-ary fields as a
    /// tree. This is the std `#18000` `LawfulVecOperator.mk` shape.
    #[test]
    fn prop_ctor_apps_convert_by_pi_not_field_tree() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let true_ty = expr::const_(1, vec![]);
        let intro = expr::const_(2, vec![]);
        env.insert(
            3,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    true_ty.clone(),
                    true_ty.clone(),
                ),
                value: expr::lam(expr::BinderInfo::Default, true_ty.clone(), expr::bvar(0)),
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let sort0 = expr::sort(level::zero());
        env.insert(
            4,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort0.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![4],
                ctors: vec![5],
                is_rec: false,
                is_unsafe: false,
            },
        );
        let mut mk_ty = expr::const_(4, vec![]);
        for _ in 0..7 {
            mk_ty = expr::pi(expr::BinderInfo::Default, true_ty.clone(), mk_ty);
        }
        env.insert(
            5,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: mk_ty,
                induct: 4,
                cidx: 0,
                num_params: 0,
                num_fields: 7,
                is_unsafe: false,
            },
        );
        let id_intro = expr::app(expr::const_(3, vec![]), intro.clone());
        let mk = expr::const_(5, vec![]);
        let mut left = mk.clone();
        let mut right = mk.clone();
        for _ in 0..7 {
            left = expr::app(left, intro.clone());
            right = expr::app(right, id_intro.clone());
        }
        let names = test_names(&["False", "True", "True.intro", "idTrue", "Cl", "Cl.mk"]);
        let tc = Checker::new(&env, &names, None, None);
        let ctx = Ctx::new();
        let intern0 = crate::expr::intern_calls();
        let ok = tc.is_def_eq(&ctx, &left, &right).expect("defeq");
        let intern_delta = crate::expr::intern_calls() - intern0;
        assert!(ok, "distinct True proofs of the same Cl must convert by PI");
        assert!(
            intern_delta < 50_000,
            "PI must not tree-walk 7-ary mk fields: intern_calls +{intern_delta}"
        );
        // Nested mk spines: `#18000` is ~15 deep. Pairwise of 7-ary fields
        // without Prop-ctor skip is exponential; PI/defeq_args must stay DAG.
        let mut nest_l = left.clone();
        let mut nest_r = right.clone();
        for _ in 0..4 {
            let mut l = mk.clone();
            let mut r = mk.clone();
            for i in 0..7 {
                l = expr::app(l, if i == 0 { nest_l.clone() } else { intro.clone() });
                r = expr::app(r, if i == 0 { nest_r.clone() } else { id_intro.clone() });
            }
            nest_l = l;
            nest_r = r;
        }
        let intern1 = crate::expr::intern_calls();
        let ok = tc.is_def_eq(&ctx, &nest_l, &nest_r).expect("nested defeq");
        let nested_delta = crate::expr::intern_calls() - intern1;
        assert!(ok, "nested Cl.mk spines must convert by Prop-ctor skip / PI");
        assert!(
            nested_delta < 50_000,
            "nested Prop-ctor spines must not tree-walk: intern_calls +{nested_delta}"
        );
    }

    /// std `#18000` instances are *large Regular defs* of a class (Prop).
    /// `obviously_not_proof` must not treat a size-capped Regular as data:
    /// PI uses the declared type, and the WHNFs (`True.intro` vs opaque `idT`
    /// of it) do not convert without PI.
    #[test]
    fn large_prop_regulars_convert_by_pi() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let true_ty = expr::const_(1, vec![]);
        let intro = expr::const_(2, vec![]);
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            3,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    true_ty.clone(),
                    true_ty.clone(),
                ),
                value: expr::lam(expr::BinderInfo::Default, true_ty.clone(), expr::bvar(0)),
                hints: ReducibilityHints::Opaque,
                is_unsafe: false,
            },
        );
        let pad = bush(true_ty.clone(), 13);
        assert!(
            expr_size_capped(&pad, 10_000) >= 4_096,
            "pad must exceed the WHNF Regular cap"
        );
        env.insert(
            4,
            ConstantInfo::Def {
                level_params: vec![],
                typ: true_ty.clone(),
                value: expr::let_(sort1.clone(), pad.clone(), intro.clone()),
                hints: ReducibilityHints::Regular(2),
                is_unsafe: false,
            },
        );
        env.insert(
            5,
            ConstantInfo::Def {
                level_params: vec![],
                typ: true_ty,
                value: expr::let_(
                    sort1,
                    pad,
                    expr::app(expr::const_(3, vec![]), intro),
                ),
                hints: ReducibilityHints::Regular(2),
                is_unsafe: false,
            },
        );
        let names = test_names(&["False", "True", "True.intro", "idT", "pA", "pB"]);
        let tc = Checker::new(&env, &names, None, None);
        let ctx = Ctx::new();
        let intern0 = crate::expr::intern_calls();
        let ok = tc
            .is_def_eq(&ctx, &expr::const_(4, vec![]), &expr::const_(5, vec![]))
            .expect("defeq");
        let intern_delta = crate::expr::intern_calls() - intern0;
        assert!(
            ok,
            "True.intro vs opaque idT True.intro, both large Regulars, must PI"
        );
        assert!(
            intern_delta < 50_000,
            "PI must not unfold the padded bodies: intern_calls +{intern_delta}"
        );
    }

    /// `#18041` instances are *lambdas* (`fun α => Mk …`). `True → True` is a
    /// Prop; Lean PI identifies `fun _ => intro` with `fun x => x`. Treating
    /// every Lam as `obviously_not_proof` forced lam-congruence of nested
    /// class-instance bodies (7^depth).
    #[test]
    fn lam_proofs_of_pi_prop_convert_by_pi() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let true_ty = expr::const_(1, vec![]);
        let intro = expr::const_(2, vec![]);
        let names = test_names(&["False", "True", "True.intro"]);
        let tc = Checker::new(&env, &names, None, None);
        let const_intro = expr::lam(expr::BinderInfo::Default, true_ty.clone(), intro);
        let identity = expr::lam(expr::BinderInfo::Default, true_ty, expr::bvar(0));
        let intern0 = crate::expr::intern_calls();
        let ok = tc
            .is_def_eq(&Ctx::new(), &const_intro, &identity)
            .expect("defeq");
        let intern_delta = crate::expr::intern_calls() - intern0;
        assert!(
            ok,
            "fun _ => True.intro and fun x => x must PI as proofs of True → True"
        );
        assert!(
            intern_delta < 50_000,
            "PI must not lam-walk bodies: intern_calls +{intern_delta}"
        );
    }

    /// `idP (elimP True.intro)`: binder is `Sort 0`, which `binder_is_prop`
    /// treats as Prop. InferOnly never sees `True.intro` vs `False`.
    #[test]
    fn idp_elimp_true_intro_sort0_rejects() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let false_ty = expr::const_(0, vec![]);
        let true_ty = expr::const_(1, vec![]);
        let sort0 = expr::sort(level::zero());
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, false_ty, sort0.clone()),
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, sort0, true_ty.clone()),
                is_unsafe: false,
            },
        );
        let junk = expr::app(expr::const_(3, vec![]), expr::const_(2, vec![]));
        env.insert(
            5,
            ConstantInfo::Theorem {
                level_params: vec![],
                typ: true_ty,
                value: expr::app(expr::const_(4, vec![]), junk),
            },
        );
        let names = test_names(&["False", "True", "True.intro", "elimP", "idP", "bad"]);
        let tc = Checker::new(&env, &names, None, None);
        assert_app_mismatch(tc.check_decl(5, "theorem"));
    }

    /// `And.intro True.intro (False.elim True.intro)`. `And.intro` is a ctor,
    /// not a recursor, so InferOnly applies to both proof fields.
    #[test]
    fn and_intro_false_elim_rejects() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let sort0 = expr::sort(level::zero());
        // And : Prop → Prop → Prop
        let and_ty = expr::pi(
            expr::BinderInfo::Default,
            sort0.clone(),
            expr::pi(expr::BinderInfo::Default, sort0.clone(), sort0.clone()),
        );
        env.insert(
            3,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: and_ty,
                num_params: 2,
                num_indices: 0,
                all: vec![3],
                ctors: vec![4],
                is_rec: false,
                is_unsafe: false,
            },
        );
        // And.intro : Π a b : Prop. a → b → And a b
        let and_a_b = expr::app(
            expr::app(expr::const_(3, vec![]), expr::bvar(3)),
            expr::bvar(2),
        );
        let intro_ty = expr::pi(
            expr::BinderInfo::Default,
            sort0.clone(),
            expr::pi(
                expr::BinderInfo::Default,
                sort0.clone(),
                expr::pi(
                    expr::BinderInfo::Default,
                    expr::bvar(1),
                    expr::pi(expr::BinderInfo::Default, expr::bvar(1), and_a_b),
                ),
            ),
        );
        env.insert(
            4,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: intro_ty,
                induct: 3,
                cidx: 0,
                num_params: 2,
                num_fields: 2,
                is_unsafe: false,
            },
        );
        env.insert(
            5,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    expr::const_(0, vec![]),
                    expr::const_(1, vec![]),
                ),
                is_unsafe: false,
            },
        );
        let t = expr::const_(1, vec![]);
        let intro = expr::const_(2, vec![]);
        let junk = expr::app(expr::const_(5, vec![]), intro.clone());
        let value = expr::apps(expr::const_(4, vec![]), &[t.clone(), t.clone(), intro, junk]);
        env.insert(
            6,
            ConstantInfo::Theorem {
                level_params: vec![],
                typ: expr::app(expr::app(expr::const_(3, vec![]), t.clone()), t),
                value,
            },
        );
        let names = test_names(&[
            "False",
            "True",
            "True.intro",
            "And",
            "And.intro",
            "elim",
            "bad",
        ]);
        let tc = Checker::new(&env, &names, None, None);
        assert_app_mismatch(tc.check_decl(6, "theorem"));
    }

    /// `closed_int_value` currently treats `Lit Nat n` and `OfNat.ofNat Int n`
    /// as the same integer, so the terms defeq. Lean conversion does not.
    #[test]
    fn heq_nat_vs_int_numeral_not_defeq() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        // OfNat.ofNat : {α} → Nat → {OfNat α} → α  (we only need the name + ≥2 args)
        env.insert(
            2,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    sort1.clone(),
                    expr::pi(
                        expr::BinderInfo::Default,
                        expr::const_(0, vec![]),
                        expr::pi(
                            expr::BinderInfo::Default,
                            expr::sort(level::zero()),
                            expr::bvar(2),
                        ),
                    ),
                ),
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::sort(level::zero()),
                is_unsafe: false,
            },
        );
        let names = test_names(&["Nat", "Int", "OfNat.ofNat", "inst"]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let n3 = expr::lit_nat(3u32.into());
        let int3 = expr::apps(
            expr::const_(2, vec![]),
            &[
                expr::const_(1, vec![]),
                n3.clone(),
                expr::const_(3, vec![]),
            ],
        );
        let eq = tc.is_def_eq(&Ctx::new(), &n3, &int3).unwrap();
        assert!(
            !eq,
            "Nat literal 3 must not defeq OfNat.ofNat Int 3 inst"
        );
    }

    /// Parsing closed integers is an evaluator aid, not a conversion rule.
    /// An unrelated `Shadow.Int.add` axiom must not become definitionally
    /// equal to the integer numeral computed from its arguments.
    #[test]
    fn namespaced_int_axiom_is_not_defeq_computed_numeral() {
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        axiom_sort(&mut env, 0, sort1.clone()); // Nat
        axiom_sort(&mut env, 1, sort1); // Int
        let nat = expr::const_(0, vec![]);
        let int = expr::const_(1, vec![]);
        axiom_sort(
            &mut env,
            2,
            expr::pi(expr::BinderInfo::Default, nat, int.clone()),
        ); // Int.ofNat
        axiom_sort(
            &mut env,
            3,
            expr::pi(
                expr::BinderInfo::Default,
                int.clone(),
                expr::pi(expr::BinderInfo::Default, int.clone(), int),
            ),
        ); // Shadow.Int.add
        let names = test_names(&["Nat", "Int", "Int.ofNat", "Shadow.Int.add"]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let of_nat = |n: u32| expr::app(expr::const_(2, vec![]), expr::lit_nat(n.into()));
        let shadow_add = expr::apps(expr::const_(3, vec![]), &[of_nat(1), of_nat(2)]);
        assert!(
            !tc.is_def_eq(&Ctx::new(), &shadow_add, &of_nat(3))
                .expect("defeq"),
            "Shadow.Int.add 1 2 is stuck and must not convert to Int.ofNat 3"
        );
    }

    /// `Nat.cast` must not identify numerals at unrelated types.
    #[test]
    fn nat_cast_nat_vs_int_not_defeq() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    sort1.clone(),
                    expr::pi(
                        expr::BinderInfo::Default,
                        expr::sort(level::zero()),
                        expr::pi(
                            expr::BinderInfo::Default,
                            expr::const_(0, vec![]),
                            expr::bvar(2),
                        ),
                    ),
                ),
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::sort(level::zero()),
                is_unsafe: false,
            },
        );
        let names = test_names(&["Nat", "Int", "Nat.cast", "inst"]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let n3 = expr::lit_nat(3u32.into());
        let cast = |ty: u32| {
            expr::apps(
                expr::const_(2, vec![]),
                &[
                    expr::const_(ty, vec![]),
                    expr::const_(3, vec![]),
                    n3.clone(),
                ],
            )
        };
        let eq = tc
            .is_def_eq(&Ctx::new(), &cast(0), &cast(1))
            .unwrap();
        assert!(!eq, "Nat.cast Nat 3 must not defeq Nat.cast Int 3");
    }

    /// An axiom with the exact library name `Lean.Grind.CommRing.norm_eq_cert`
    /// must not WHNF to `Bool.true` even when its arguments parse as equal
    /// monomials. Exact spelling does not turn an axiom into a definition.
    #[test]
    fn canonical_commring_axiom_does_not_whnf_true() {
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        let sort0 = expr::sort(level::zero());
        axiom_sort(&mut env, 0, sort1.clone()); // Nat
        axiom_sort(&mut env, 1, sort1.clone()); // Int
        axiom_sort(
            &mut env,
            2,
            expr::pi(
                expr::BinderInfo::Default,
                expr::const_(0, vec![]),
                expr::const_(1, vec![]),
            ),
        ); // Int.ofNat
        axiom_sort(&mut env, 3, sort0.clone()); // Bool.true
        axiom_sort(&mut env, 4, sort0.clone()); // Bool.false
        axiom_sort(
            &mut env,
            5,
            expr::pi(
                expr::BinderInfo::Default,
                expr::const_(1, vec![]),
                sort0.clone(),
            ),
        ); // Lean.Grind.CommRing.Expr.num
        let bool_ty = sort0.clone();
        let expr_ty = sort0;
        let cert_ty = expr::pi(
            expr::BinderInfo::Default,
            expr_ty.clone(),
            expr::pi(
                expr::BinderInfo::Default,
                expr_ty.clone(),
                expr::pi(
                    expr::BinderInfo::Default,
                    expr_ty.clone(),
                    expr::pi(expr::BinderInfo::Default, expr_ty, bool_ty),
                ),
            ),
        );
        axiom_sort(&mut env, 6, cert_ty); // Lean.Grind.CommRing.norm_eq_cert
        let names = test_names(&[
            "Nat",
            "Int",
            "Int.ofNat",
            "Bool.true",
            "Bool.false",
            "Lean.Grind.CommRing.Expr.num",
            "Lean.Grind.CommRing.norm_eq_cert",
        ]);
        let tc = Checker::new(&env, &names, None, None);
        let z = expr::app(expr::const_(2, vec![]), expr::lit_nat(0u32.into()));
        let num = expr::app(expr::const_(5, vec![]), z);
        let cert = expr::apps(
            expr::const_(6, vec![]),
            &[num.clone(), num.clone(), num.clone(), num],
        );
        let w = tc.whnf(&Ctx::new(), &cert).expect("WHNF");
        let (h, _) = expr::unfold_apps(&w);
        let reduced_true = matches!(&**h, ExprData::Const(n, _) if *n == 3);
        assert!(
            !reduced_true,
            "axiom Lean.Grind.CommRing.norm_eq_cert must stay stuck, got {}",
            tc.pp(&w)
        );
    }

    /// Inductive `Foo.Int` is not Lean `Int`: HAdd/cast must not rewrite.
    #[test]
    fn foo_int_is_not_int_for_hadd() {
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        axiom_sort(&mut env, 0, sort1.clone()); // Nat
        env.insert(
            1,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort1.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![1],
                ctors: vec![],
                is_rec: false,
                is_unsafe: false,
            },
        ); // Foo.Int
        axiom_sort(&mut env, 2, sort1.clone()); // Int
        let bin = expr::pi(
            expr::BinderInfo::Default,
            expr::const_(2, vec![]),
            expr::pi(
                expr::BinderInfo::Default,
                expr::const_(2, vec![]),
                expr::const_(2, vec![]),
            ),
        );
        axiom_sort(&mut env, 3, bin); // Int.add
        let star = expr::sort(level::zero());
        let hadd_ty = expr::pi(
            expr::BinderInfo::Default,
            sort1.clone(),
            expr::pi(
                expr::BinderInfo::Default,
                sort1.clone(),
                expr::pi(
                    expr::BinderInfo::Default,
                    sort1,
                    expr::pi(
                        expr::BinderInfo::Default,
                        star.clone(),
                        expr::pi(
                            expr::BinderInfo::Default,
                            star.clone(),
                            expr::pi(expr::BinderInfo::Default, star.clone(), star),
                        ),
                    ),
                ),
            ),
        );
        axiom_sort(&mut env, 4, hadd_ty); // HAdd.hAdd
        axiom_sort(&mut env, 5, expr::sort(level::zero())); // inst
        axiom_sort(&mut env, 6, expr::const_(1, vec![])); // x
        axiom_sort(&mut env, 7, expr::const_(1, vec![])); // y
        let names = test_names(&[
            "Nat",
            "Foo.Int",
            "Int",
            "Int.add",
            "HAdd.hAdd",
            "inst",
            "x",
            "y",
        ]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let foo = expr::const_(1, vec![]);
        assert!(
            !tc.type_head_is_int(&foo),
            "Foo.Int must not be Int for HAdd/cast"
        );
        let e = expr::apps(
            expr::const_(4, vec![]),
            &[
                foo.clone(),
                foo.clone(),
                foo,
                expr::const_(5, vec![]),
                expr::const_(6, vec![]),
                expr::const_(7, vec![]),
            ],
        );
        let w = tc.whnf(&Ctx::new(), &e).expect("WHNF");
        let (h, _) = expr::unfold_apps(&w);
        let became_int_add = matches!(&**h, ExprData::Const(n, _) if *n == 3);
        assert!(
            !became_int_add,
            "HAdd on Foo.Int must not rewrite to Int.add, got {}",
            tc.pp(&w)
        );
    }

    /// Kernel must not synthesize `isTrue True True.intro` for `Int.decLe`.
    #[test]
    fn int_dec_le_does_not_synthesize_istrue_true() {
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        let sort0 = expr::sort(level::zero());
        axiom_sort(&mut env, 0, sort1.clone()); // Nat
        axiom_sort(&mut env, 1, sort1); // Int
        axiom_sort(
            &mut env,
            2,
            expr::pi(
                expr::BinderInfo::Default,
                expr::const_(0, vec![]),
                expr::const_(1, vec![]),
            ),
        ); // Int.ofNat
        axiom_sort(&mut env, 3, sort0.clone()); // True
        axiom_sort(&mut env, 4, expr::const_(3, vec![])); // True.intro
        axiom_sort(
            &mut env,
            5,
            expr::pi(
                expr::BinderInfo::Default,
                sort0.clone(),
                expr::pi(
                    expr::BinderInfo::Default,
                    expr::bvar(0),
                    expr::sort(level::zero()),
                ),
            ),
        ); // Decidable.isTrue
        axiom_sort(
            &mut env,
            6,
            expr::pi(
                expr::BinderInfo::Default,
                expr::const_(1, vec![]),
                expr::pi(
                    expr::BinderInfo::Default,
                    expr::const_(1, vec![]),
                    expr::sort(level::zero()),
                ),
            ),
        ); // Int.decLe
        let names = test_names(&[
            "Nat",
            "Int",
            "Int.ofNat",
            "True",
            "True.intro",
            "Decidable.isTrue",
            "Int.decLe",
        ]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let ofn = |n: u32| expr::app(expr::const_(2, vec![]), expr::lit_nat(n.into()));
        let e = expr::apps(expr::const_(6, vec![]), &[ofn(0), ofn(1)]);
        let w = tc.whnf(&Ctx::new(), &e).expect("WHNF");
        let (h, args) = expr::unfold_apps(&w);
        let is_true_true = matches!(&**h, ExprData::Const(n, _) if *n == 5)
            && args
                .first()
                .is_some_and(|a| matches!(&***a, ExprData::Const(t, _) if *t == 3));
        assert!(
            !is_true_true,
            "Int.decLe must not WHNF to isTrue True True.intro, got {}",
            tc.pp(&w)
        );
    }

    /// Proj ι only if the constructor belongs to the projected inductive.
    #[test]
    fn proj_wrong_inductive_does_not_iota() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort1.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![1],
                ctors: vec![2],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    expr::const_(0, vec![]),
                    expr::const_(1, vec![]),
                ),
                induct: 1,
                cidx: 0,
                num_params: 0,
                num_fields: 1,
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort1,
                num_params: 0,
                num_indices: 0,
                all: vec![3],
                ctors: vec![4],
                is_rec: false,
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    expr::const_(0, vec![]),
                    expr::const_(3, vec![]),
                ),
                induct: 3,
                cidx: 0,
                num_params: 0,
                num_fields: 1,
                is_unsafe: false,
            },
        );
        let names = test_names(&["Nat", "A", "A.mk", "B", "B.mk"]);
        let tc = Checker::new(&env, &names, None, None);
        let n3 = expr::lit_nat(3u32.into());
        let amk = expr::app(expr::const_(2, vec![]), n3.clone());
        let w = tc
            .whnf(&Ctx::new(), &expr::proj(3, 0, amk))
            .expect("WHNF");
        assert!(
            !Rc::ptr_eq(&w, &n3) && !matches!(&**w, ExprData::Lit(_)),
            "proj B 0 (A.mk 3) must not ι to 3, got {}",
            tc.pp(&w)
        );
    }

    /// Lam conversion must require domains, like Pi. `fun (x : Nat) => star`
    /// is not `fun (x : Bool) => star`.
    #[test]
    fn lam_domains_must_defeq() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(0, vec![]),
                is_unsafe: false,
            },
        );
        let names = test_names(&["Nat", "Bool", "star"]);
        let tc = Checker::new(&env, &names, None, None);
        let star = expr::const_(2, vec![]);
        let f_nat = expr::lam(
            expr::BinderInfo::Default,
            expr::const_(0, vec![]),
            star.clone(),
        );
        let f_bool = expr::lam(
            expr::BinderInfo::Default,
            expr::const_(1, vec![]),
            star,
        );
        let eq = tc.is_def_eq(&Ctx::new(), &f_nat, &f_bool).unwrap();
        assert!(!eq, "lambda domains must convert, like Pi");
    }

    /// `(let f := id; f) a` must ζ then β. `StateT.bind.match_1` ι can
    /// produce a `let` under remaining args; WHNF of `App(Let, …)` is that case.
    #[test]
    fn app_of_let_zetas_then_beta() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(0, vec![]),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "a"]);
        let tc = Checker::new(&env, &names, None, None);
        let a_ty = expr::const_(0, vec![]);
        let id = expr::lam(expr::BinderInfo::Default, a_ty.clone(), expr::bvar(0));
        let arg = expr::const_(1, vec![]);
        let e = expr::app(
            expr::let_(
                expr::pi(expr::BinderInfo::Default, a_ty.clone(), a_ty),
                id,
                expr::bvar(0),
            ),
            arg.clone(),
        );
        let w = tc.whnf(&Ctx::new(), &e).expect("WHNF App(Let, arg)");
        assert!(
            Rc::ptr_eq(&w, &arg),
            "(let f := id; f) a must be a, got {}",
            tc.pp(&w)
        );
    }

    /// Same interned K-like rec app `True.rec motive minor #0` under
    /// `#0 : True` vs `#0 : False`. WHNF keyed only by ptr K-reduces in
    /// the True context then reuses that result for False (Eq.rec class).
    #[test]
    fn eq_rec_whnf_cache_is_context_sensitive() {
        use crate::env::{ConstantInfo, Environment, RecRule};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let true_ty = expr::const_(1, vec![]);
        let sort0 = expr::sort(level::zero());
        // motive : True → Prop
        let mot_ty = expr::pi(expr::BinderInfo::Default, true_ty.clone(), sort0.clone());
        // True.rec : (motive : True → Prop) → motive True.intro → (t : True) → motive t
        let rec_ty = expr::pi(
            expr::BinderInfo::Default,
            mot_ty,
            expr::pi(
                expr::BinderInfo::Default,
                expr::app(expr::bvar(0), expr::const_(2, vec![])),
                expr::pi(
                    expr::BinderInfo::Default,
                    true_ty.clone(),
                    expr::app(expr::bvar(2), expr::bvar(0)),
                ),
            ),
        );
        env.insert(
            3,
            ConstantInfo::Recursor {
                level_params: vec![],
                typ: rec_ty,
                all: vec![1],
                num_params: 0,
                num_indices: 0,
                num_motives: 1,
                num_minors: 1,
                rules: vec![RecRule {
                    ctor: 2,
                    nfields: 0,
                    rhs: expr::bvar(0),
                }],
                k: true,
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort0.clone(),
                is_unsafe: false,
            },
        );
        env.rec_of.insert(1, 3);
        let names = test_names(&["False", "True", "True.intro", "True.rec", "star"]);
        let tc = Checker::new(&env, &names, None, None);
        let motive = expr::lam(expr::BinderInfo::Default, true_ty, sort0);
        let star = expr::const_(4, vec![]);
        let rec_app = expr::apps(expr::const_(3, vec![]), &[motive, star.clone(), expr::bvar(0)]);
        let mut ctx_true = Ctx::new();
        ctx_true.push(expr::const_(1, vec![]));
        let mut ctx_false = Ctx::new();
        ctx_false.push(expr::const_(0, vec![]));
        let w_true = tc.whnf(&ctx_true, &rec_app).expect("WHNF True context");
        assert!(
            Rc::ptr_eq(&w_true, &star),
            "K-like True.rec under #0 : True must reduce to the minor, got {}",
            tc.pp(&w_true)
        );
        let w_false = tc.whnf(&ctx_false, &rec_app).expect("WHNF False context");
        assert!(
            !Rc::ptr_eq(&w_false, &star),
            "WHNF of the same rec app under #0 : False must not reuse the True-context K-reduction"
        );
    }

    /// Mini `PSigma` (2 params, 1 ctor, 0 indices, not rec). Lean
    /// `to_ctor_when_structure` expands a bvar major to `mk e.1 e.2` so
    /// `PSigma.rec motive minor x` iotas to `minor x.1 x.2`.
    fn insert_mini_psigma(env: &mut Environment) {
        let sort1 = expr::sort(level::succ(level::zero()));
        let psigma = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    sort1.clone(),
                    expr::pi(expr::BinderInfo::Default, sort1.clone(), sort1.clone()),
                ),
                num_params: 2,
                num_indices: 0,
                all: vec![0],
                ctors: vec![1],
                is_rec: false,
                is_unsafe: false,
            },
        );
        // mk : (α β : Type) → α → β → PSigma α β
        let mk_ty = expr::pi(
            expr::BinderInfo::Default,
            sort1.clone(),
            expr::pi(
                expr::BinderInfo::Default,
                sort1.clone(),
                expr::pi(
                    expr::BinderInfo::Default,
                    expr::bvar(1),
                    expr::pi(
                        expr::BinderInfo::Default,
                        expr::bvar(1),
                        expr::apps(psigma, &[expr::bvar(3), expr::bvar(2)]),
                    ),
                ),
            ),
        );
        env.insert(
            1,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: mk_ty,
                induct: 0,
                cidx: 0,
                num_params: 2,
                num_fields: 2,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Recursor {
                level_params: vec![],
                typ: sort1.clone(),
                all: vec![0],
                num_params: 2,
                num_indices: 0,
                num_motives: 1,
                num_minors: 1,
                rules: vec![crate::env::RecRule {
                    ctor: 1,
                    nfields: 2,
                    rhs: expr::bvar(0),
                }],
                k: false,
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1,
                is_unsafe: false,
            },
        );
        env.rec_of.insert(0, 2);
    }

    /// `PSigma.rec α β motive minor (mk α β x y)` iotas to `minor x y`.
    #[test]
    fn psigma_rec_iotas_ctor_major() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let names = test_names(&["PSigma", "PSigma.mk", "PSigma.rec", "A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(3, vec![]);
        let b = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a.clone(), b.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab, sort1);
        let minor = expr::lam(
            expr::BinderInfo::Default,
            a.clone(),
            expr::lam(expr::BinderInfo::Default, b.clone(), expr::bvar(1)),
        );
        let x = expr::const_(3, vec![]); // A : Type used as a dummy value of type A (ill-typed but WHNF-only)
        let y = expr::const_(4, vec![]);
        let mk = expr::apps(expr::const_(1, vec![]), &[a.clone(), b, x.clone(), y]);
        let rec_app = expr::apps(
            expr::const_(2, vec![]),
            &[a, expr::const_(4, vec![]), motive, minor, mk],
        );
        let w = tc.whnf(&Ctx::new(), &rec_app).expect("WHNF ctor major");
        assert!(
            Rc::ptr_eq(&w, &x),
            "PSigma.rec of mk x y must iota to minor x y = x, got {}",
            tc.pp(&w)
        );
    }

    /// `PSigma.rec α β motive minor #0` under `#0 : PSigma α β` must expand
    /// the bvar to `mk #0.1 #0.2` and iota. std
    /// `toGraphviz.go._unary.eq_def` is this case (`PSigma.casesOn` → rec).
    #[test]
    fn psigma_rec_iotas_bvar_major() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let names = test_names(&["PSigma", "PSigma.mk", "PSigma.rec", "A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(3, vec![]);
        let b = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a.clone(), b.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab.clone(), sort1);
        let minor = expr::lam(
            expr::BinderInfo::Default,
            a.clone(),
            expr::lam(expr::BinderInfo::Default, b.clone(), expr::bvar(1)),
        );
        let rec_app = expr::apps(
            expr::const_(2, vec![]),
            &[a, b, motive, minor, expr::bvar(0)],
        );
        let mut ctx = Ctx::new();
        ctx.push(psigma_ab);
        let w = tc.whnf(&ctx, &rec_app).expect("WHNF bvar major");
        let expected = expr::proj(0, 0, expr::bvar(0));
        assert!(
            tc.is_def_eq(&ctx, &w, &expected).unwrap_or(false),
            "PSigma.rec of a PSigma bvar must iota to minor (proj 0) (proj 1) = proj 0, got {}",
            tc.pp(&w)
        );
    }

    /// `Π x : A, (λ y : A, T) x` converts to `Π x : A, T`.
    /// `toGraphviz.go._unary.eq_def` Eq args include this Pi-beta.
    #[test]
    fn pi_body_beta_converts() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1,
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "T"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(0, vec![]);
        let t = expr::const_(1, vec![]);
        let redex = expr::pi(
            expr::BinderInfo::Default,
            a.clone(),
            expr::app(
                expr::lam(expr::BinderInfo::Default, a.clone(), t.clone()),
                expr::bvar(0),
            ),
        );
        let nf = expr::pi(expr::BinderInfo::Default, a, t);
        let eq = tc.is_def_eq(&Ctx::new(), &redex, &nf).unwrap();
        assert!(eq, "Pi body must beta: (λ y, T) x ≡ T");
    }

    /// CORE_DEPTH abort must Decline. Returning the unreduced `id a` as
    /// WHNF makes `id a ≡ a` Ok(false) at the cap (stuck term as normal form).
    #[test]
    fn core_depth_abort_declines_not_stuck_whnf() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(0, vec![]),
                is_unsafe: false,
            },
        );
        let a_ty = expr::const_(0, vec![]);
        env.insert(
            2,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    a_ty.clone(),
                    a_ty.clone(),
                ),
                value: expr::lam(expr::BinderInfo::Default, a_ty, expr::bvar(0)),
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "a", "id"]);
        let tc = Checker::new(&env, &names, None, None);
        let id_a = expr::app(expr::const_(2, vec![]), expr::const_(1, vec![]));
        CORE_DEPTH.with(|d| d.set(CONV_DEPTH));
        CORE_ABORTED.with(|a| a.set(false));
        let wh = tc.whnf(&Ctx::new(), &id_a);
        let eq = tc.is_def_eq(&Ctx::new(), &id_a, &expr::const_(1, vec![]));
        CORE_DEPTH.with(|d| d.set(0));
        CORE_ABORTED.with(|a| a.set(false));
        match wh {
            Err(TcError::Decline(_)) => {}
            other => panic!("CORE_DEPTH abort must Decline unreduced `id a`, got {other:?}"),
        }
        match eq {
            Err(TcError::Decline(_)) => {}
            other => panic!("CORE_DEPTH abort must Decline defeq, not {other:?}"),
        }
        // Stuck axiom is already WHNF. Treating it as a core redex Declines
        // Init `Int16.ofInt_eq_ofNat` / `Nat.rec`.
        CORE_DEPTH.with(|d| d.set(CONV_DEPTH));
        CORE_ABORTED.with(|a| a.set(false));
        let stuck = tc.whnf(&Ctx::new(), &expr::const_(1, vec![]));
        CORE_DEPTH.with(|d| d.set(0));
        CORE_ABORTED.with(|a| a.set(false));
        match stuck {
            Ok(_) => {}
            other => panic!("stuck axiom at CORE_DEPTH must not Decline, got {other:?}"),
        }
    }

    /// Decline during is_prop/PI must not be stored as `false` in defeq_cache.
    /// `p intro` / `q intro` with `p, q : ((λ _. True → True) a)`: infer of the
    /// apps hits a β-redex type; the apps themselves are stuck axiom heads
    /// (not core redexes), so a swallowed Decline would cache `false`.
    #[test]
    fn decline_during_pi_not_cached_as_false() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        insert_false_true(&mut env);
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            3,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1,
                is_unsafe: false,
            },
        );
        env.insert(
            4,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(3, vec![]),
                is_unsafe: false,
            },
        );
        let true_ty = expr::const_(1, vec![]);
        let a_ty = expr::const_(3, vec![]);
        let a = expr::const_(4, vec![]);
        let true_to_true = expr::pi(expr::BinderInfo::Default, true_ty.clone(), true_ty.clone());
        let wrap = expr::app(expr::lam(expr::BinderInfo::Default, a_ty, true_to_true), a);
        env.insert(
            5,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: wrap.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            6,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: wrap,
                is_unsafe: false,
            },
        );
        let names = test_names(&["False", "True", "True.intro", "A", "a", "p", "q"]);
        let tc = Checker::new(&env, &names, None, None);
        let intro = expr::const_(2, vec![]);
        let p_app = expr::app(expr::const_(5, vec![]), intro.clone());
        let q_app = expr::app(expr::const_(6, vec![]), intro);
        CORE_DEPTH.with(|d| d.set(CONV_DEPTH));
        CORE_ABORTED.with(|a| a.set(false));
        let first = tc.is_def_eq(&Ctx::new(), &p_app, &q_app);
        CORE_DEPTH.with(|d| d.set(0));
        CORE_ABORTED.with(|a| a.set(false));
        match first {
            Err(TcError::Decline(_)) => {}
            other => panic!("PI/is_prop at CORE_DEPTH must Decline, got {other:?}"),
        }
        let second = tc
            .is_def_eq(&Ctx::new(), &p_app, &q_app)
            .expect("defeq after reset");
        assert!(
            second,
            "Decline during PI must not cache false; p intro and q intro are proofs of True"
        );
    }

    /// A ctor-major recursor at CONV_DEPTH is returned without caching. A later
    /// call at ordinary depth must still iota-reduce it.
    #[test]
    fn core_depth_abort_does_not_cache_recursor() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let names = test_names(&["PSigma", "PSigma.mk", "PSigma.rec", "A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(3, vec![]);
        let b = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a.clone(), b.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab, sort1);
        let minor = expr::lam(
            expr::BinderInfo::Default,
            a.clone(),
            expr::lam(expr::BinderInfo::Default, b.clone(), expr::bvar(1)),
        );
        let x = expr::const_(3, vec![]);
        let y = expr::const_(4, vec![]);
        let mk = expr::apps(expr::const_(1, vec![]), &[a.clone(), b, x.clone(), y]);
        let rec_app = expr::apps(
            expr::const_(2, vec![]),
            &[a, expr::const_(4, vec![]), motive, minor, mk],
        );
        CORE_DEPTH.with(|d| d.set(CONV_DEPTH));
        CORE_ABORTED.with(|ab| ab.set(false));
        let at_cap = tc.whnf(&Ctx::new(), &rec_app);
        CORE_DEPTH.with(|d| d.set(0));
        CORE_ABORTED.with(|ab| ab.set(false));
        match at_cap {
            Err(TcError::Decline(_)) => {}
            other => panic!("recursor app at CORE_DEPTH must Decline, got {other:?}"),
        }
        let w = tc.whnf(&Ctx::new(), &rec_app).expect("WHNF after reset");
        assert!(
            Rc::ptr_eq(&w, &x),
            "abort must not cache a stuck rec app; later WHNF must ι, got {}",
            tc.pp(&w)
        );
    }

    /// Let-zeta is part of WHNF. Defeq of `let x := v; x` vs `v` must hold
    /// even if a CORE_DEPTH abort previously saw the unreduced let.
    #[test]
    fn let_zetas_in_defeq() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(0, vec![]),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "v"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(0, vec![]);
        let v = expr::const_(1, vec![]);
        let let_e = expr::let_(a, v.clone(), expr::bvar(0));
        let eq = tc.is_def_eq(&Ctx::new(), &let_e, &v).unwrap();
        assert!(eq, "let x := v; x must convert to v");
        let w = tc.whnf(&Ctx::new(), &let_e).unwrap();
        assert!(
            Rc::ptr_eq(&w, &v),
            "WHNF of let x := v; x must be v, got {}",
            tc.pp(&w)
        );
    }

    /// `Π x : A, ((λ y : A, F #2) x) ≡ Π x : A, F #1`.
    /// The `#2` lives outside the Pi; beta must decrement it. `eq_def`'s
    /// `Π String. ((λ String. Π PSigma. StateM) #0)` has this shape with
    /// HashSet/Array.size bvars.
    #[test]
    fn pi_body_beta_decrements_outer_bvars() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        // F : Type → Type
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, sort1.clone(), sort1),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "F"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(0, vec![]);
        let f = expr::const_(1, vec![]);
        let redex = expr::pi(
            expr::BinderInfo::Default,
            a.clone(),
            expr::app(
                expr::lam(
                    expr::BinderInfo::Default,
                    a.clone(),
                    expr::app(f.clone(), expr::bvar(2)),
                ),
                expr::bvar(0),
            ),
        );
        let nf = expr::pi(
            expr::BinderInfo::Default,
            a,
            expr::app(f, expr::bvar(1)),
        );
        let eq = tc.is_def_eq(&Ctx::new(), &redex, &nf).unwrap();
        assert!(
            eq,
            "Pi-body beta must decrement outer bvars: got {} vs {}",
            tc.pp(&redex),
            tc.pp(&nf)
        );
    }

    /// Inner lambda domain is a beta redex: `λ x : A, λ y : ((λ _ : A, B) x), y`
    /// vs `λ x : A, λ y : B, y`. congrArg on `toGraphviz.go._unary.eq_def`
    /// has `λ ((λ String. PSigma …) #0). …` on one Eq side.
    #[test]
    fn lam_domain_beta_redex_converts() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1,
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(0, vec![]);
        let b = expr::const_(1, vec![]);
        let redex = expr::lam(
            expr::BinderInfo::Default,
            a.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                expr::app(
                    expr::lam(expr::BinderInfo::Default, a.clone(), b.clone()),
                    expr::bvar(0),
                ),
                expr::bvar(0),
            ),
        );
        let nf = expr::lam(
            expr::BinderInfo::Default,
            a,
            expr::lam(expr::BinderInfo::Default, b, expr::bvar(0)),
        );
        let eq = tc.is_def_eq(&Ctx::new(), &redex, &nf).unwrap();
        assert!(
            eq,
            "lambda domain beta must convert: got {} vs {}",
            tc.pp(&redex),
            tc.pp(&nf)
        );
    }

    /// `PSigma.rec motive (λ a b, f a b) p ≡ f p.1 p.2`. After ι the rec
    /// is the applied minor; Bind.bind minors in `eq_def` are this shape.
    #[test]
    fn psigma_rec_defeq_proj_applied_minor() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let names = test_names(&["PSigma", "PSigma.mk", "PSigma.rec", "A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(3, vec![]);
        let b = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a.clone(), b.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab.clone(), sort1);
        let minor = expr::lam(
            expr::BinderInfo::Default,
            a.clone(),
            expr::lam(expr::BinderInfo::Default, b.clone(), expr::bvar(1)),
        );
        let rec_app = expr::apps(
            expr::const_(2, vec![]),
            &[a, b, motive, minor, expr::bvar(0)],
        );
        let mut ctx = Ctx::new();
        ctx.push(psigma_ab);
        let applied = expr::proj(0, 0, expr::bvar(0));
        assert!(
            tc.is_def_eq(&ctx, &rec_app, &applied).unwrap_or(false),
            "rec on a PSigma bvar must convert to the minor of projections, got {} vs {}",
            tc.pp(&tc.whnf(&ctx, &rec_app).unwrap_or_else(|_| rec_app.clone())),
            tc.pp(&applied)
        );
    }

    /// Abbrev `match_1 t minor := rec (λ a b, minor a b) t` (StateT.bind.match_1
    /// shape). WHNF and defeq must ι through the Abbrev, not compare the
    /// unreduced minors `λ a b, a` vs `λ a b, p.1`.
    #[test]
    fn bind_match_abbrev_iotas_then_defeq_unpacked_vs_proj() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let a_ty = expr::const_(3, vec![]);
        let b_ty = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a_ty.clone(), b_ty.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab.clone(), sort1);
        // match_1 t minor := rec A B motive (λ a b, minor a b) t
        let minor_ty = expr::pi(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::pi(expr::BinderInfo::Default, b_ty.clone(), a_ty.clone()),
        );
        let match_val = expr::lam(
            expr::BinderInfo::Default,
            psigma_ab.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                minor_ty.clone(),
                expr::apps(
                    expr::const_(2, vec![]),
                    &[
                        a_ty.clone(),
                        b_ty.clone(),
                        motive,
                        expr::lam(
                            expr::BinderInfo::Default,
                            a_ty.clone(),
                            expr::lam(
                                expr::BinderInfo::Default,
                                b_ty.clone(),
                                expr::apps(expr::bvar(2), &[expr::bvar(1), expr::bvar(0)]),
                            ),
                        ),
                        expr::bvar(1),
                    ],
                ),
            ),
        );
        env.insert(
            5,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(
                    expr::BinderInfo::Default,
                    psigma_ab.clone(),
                    expr::pi(expr::BinderInfo::Default, minor_ty, a_ty.clone()),
                ),
                value: match_val,
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let names = test_names(&[
            "PSigma",
            "PSigma.mk",
            "PSigma.rec",
            "A",
            "B",
            "match_1",
        ]);
        let tc = Checker::new(&env, &names, None, None);
        let mut ctx = Ctx::new();
        ctx.push(psigma_ab);
        let unpacked = expr::lam(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::lam(expr::BinderInfo::Default, b_ty, expr::bvar(1)),
        );
        // Continuation that ignores a,b and reads the major via projections —
        // the Bind.bind minor mismatch in eq_def.
        let via_proj = expr::lam(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                expr::const_(4, vec![]),
                expr::proj(0, 0, expr::bvar(2)),
            ),
        );
        let m_unpacked = expr::apps(expr::const_(5, vec![]), &[expr::bvar(0), unpacked]);
        let m_proj = expr::apps(expr::const_(5, vec![]), &[expr::bvar(0), via_proj]);
        let w = tc.whnf(&ctx, &m_unpacked).expect("WHNF match_1 unpacked");
        let expected = expr::proj(0, 0, expr::bvar(0));
        assert!(
            tc.is_def_eq(&ctx, &w, &expected).unwrap_or(false),
            "match_1 Abbrev must ι to minor of projs, WHNF got {}",
            tc.pp(&w)
        );
        assert!(
            tc.is_def_eq(&ctx, &m_unpacked, &m_proj).unwrap_or(false),
            "match_1 (λ a b, a) must convert to match_1 (λ a b, p.1) after ι, left={} right={}",
            tc.pp(&tc.whnf(&ctx, &m_unpacked).unwrap_or_else(|_| m_unpacked.clone())),
            tc.pp(&tc.whnf(&ctx, &m_proj).unwrap_or_else(|_| m_proj.clone()))
        );
        // StateT.bind.match_1 ι yields `let Fin := mk a b; …`. WHNF must ζ
        // that let, not return it as a stuck value (`WHNFHEAD match_1 -> let`).
        let via_let = expr::lam(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                expr::const_(4, vec![]),
                expr::let_(a_ty.clone(), expr::bvar(1), expr::bvar(0)),
            ),
        );
        let m_let = expr::apps(expr::const_(5, vec![]), &[expr::bvar(0), via_let]);
        let wlet = tc.whnf(&ctx, &m_let).expect("WHNF match_1 let-minor");
        assert!(
            !matches!(&**wlet, ExprData::Let(_, _, _)),
            "WHNF of match_1 with a let-minor must ζ, got {}",
            tc.pp(&wlet)
        );
        assert!(
            tc.is_def_eq(&ctx, &wlet, &expected).unwrap_or(false),
            "let-minor match_1 must convert to p.1, got {}",
            tc.pp(&wlet)
        );
    }

    /// `λ p, PSigma.casesOn … p minor` ≡ `λ p, PSigma.rec … (λ a b, minor a b) p`.
    /// This is the Eq-argument pair that std `#81930` fails to convert.
    #[test]
    fn cases_on_lambda_converts_to_rec_lambda() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let a_ty = expr::const_(3, vec![]);
        let b_ty = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a_ty.clone(), b_ty.clone()]);
        let sort1 = expr::sort(level::succ(level::zero()));
        let motive = expr::lam(expr::BinderInfo::Default, psigma_ab.clone(), a_ty.clone());
        let minor_ty = expr::pi(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::pi(expr::BinderInfo::Default, b_ty.clone(), a_ty.clone()),
        );
        // casesOn α β motive t minor := rec α β motive (λ a b, minor a b) t
        let cases_val = expr::lam(
            expr::BinderInfo::Default,
            sort1.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                sort1.clone(),
                expr::lam(
                    expr::BinderInfo::Default,
                    expr::pi(expr::BinderInfo::Default, psigma_ab.clone(), sort1.clone()),
                    expr::lam(
                        expr::BinderInfo::Default,
                        psigma_ab.clone(),
                        expr::lam(
                            expr::BinderInfo::Default,
                            minor_ty.clone(),
                            expr::apps(
                                expr::const_(2, vec![]),
                                &[
                                    expr::bvar(4),
                                    expr::bvar(3),
                                    expr::bvar(2),
                                    expr::lam(
                                        expr::BinderInfo::Default,
                                        a_ty.clone(),
                                        expr::lam(
                                            expr::BinderInfo::Default,
                                            b_ty.clone(),
                                            expr::apps(
                                                expr::bvar(2),
                                                &[expr::bvar(1), expr::bvar(0)],
                                            ),
                                        ),
                                    ),
                                    expr::bvar(1),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        );
        env.insert(
            5,
            ConstantInfo::Def {
                level_params: vec![],
                typ: sort1,
                value: cases_val,
                hints: ReducibilityHints::Abbrev,
                is_unsafe: false,
            },
        );
        let names = test_names(&[
            "PSigma",
            "PSigma.mk",
            "PSigma.rec",
            "A",
            "B",
            "PSigma.casesOn",
        ]);
        let tc = Checker::new(&env, &names, None, None);
        let minor = expr::lam(
            expr::BinderInfo::Default,
            a_ty.clone(),
            expr::lam(expr::BinderInfo::Default, b_ty.clone(), expr::bvar(1)),
        );
        let cases_app = expr::apps(
            expr::const_(5, vec![]),
            &[
                a_ty.clone(),
                b_ty.clone(),
                motive.clone(),
                expr::bvar(0),
                minor.clone(),
            ],
        );
        // Rec with the same minor; casesOn wraps it as (λ a b, minor a b).
        let rec_app = expr::apps(
            expr::const_(2, vec![]),
            &[a_ty, b_ty, motive, minor, expr::bvar(0)],
        );
        let lam_cases = expr::lam(
            expr::BinderInfo::Default,
            psigma_ab.clone(),
            cases_app,
        );
        let lam_rec = expr::lam(expr::BinderInfo::Default, psigma_ab, rec_app);
        let eq = tc.is_def_eq(&Ctx::new(), &lam_cases, &lam_rec).unwrap_or(false);
        assert!(
            eq,
            "λ p, casesOn p minor must convert to λ p, rec (λ a b, minor a b) p"
        );
    }

    /// Lean `is_delta` is `has_value`. A Regular whose body is larger than the
    /// WHNF eager cap must still unfold on the *lazy delta* path so
    /// `Bind.bind inst.1` can reach `StateT.bind` / `match_1`.
    #[test]
    fn large_regular_defeq_via_lazy_delta() {
        use crate::env::{ConstantInfo, Environment, ReducibilityHints};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        let dummy = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1.clone(),
                is_unsafe: false,
            },
        );
        // (λ _ : pad, x) pad  ≡  x. Body ≥ 4096; Lean has_value still unfolds.
        let pad = bush(dummy.clone(), 13);
        assert!(
            expr_size_capped(&pad, 10_000) >= 4_096,
            "pad must exceed the WHNF Regular cap"
        );
        let value = expr::lam(
            expr::BinderInfo::Default,
            sort1.clone(),
            expr::app(
                expr::lam(expr::BinderInfo::Default, sort1.clone(), expr::bvar(1)),
                pad,
            ),
        );
        env.insert(
            1,
            ConstantInfo::Def {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, sort1.clone(), sort1.clone()),
                value,
                hints: ReducibilityHints::Regular(1),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "hugeId"]);
        let tc = Checker::new(&env, &names, None, None);
        let arg = dummy;
        let lhs = expr::app(expr::const_(1, vec![]), arg.clone());
        let eq = tc.is_def_eq(&Ctx::new(), &lhs, &arg).unwrap_or(false);
        assert!(
            eq,
            "lazy delta must unfold a large Regular: {} vs {}",
            tc.pp(&lhs),
            tc.pp(&arg)
        );
    }
}
