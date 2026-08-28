use crate::env::{ConstantInfo, Environment, QuotKind, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr, ExprData, Lit};
use crate::level::{self, Level};
use crate::nat;
use crate::nbe;
use num_bigint::{BigInt, BigUint, Sign};
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

thread_local! {
    /// Recursion guard for `pub fn infer_type`'s `KIOTA_NBE=1` dispatch,
    /// mirroring `DEFEQ_DEPTH`/`WHNF_DEPTH`/`CORE_DEPTH`'s existing use of
    /// `CONV_DEPTH` as a shared cap: a genuine bug in the fallback chain
    /// between `infer_type_via_nbe` and eager (confirmed once already —
    /// `infer_type_value_fallback` calling the dispatching `infer_type`
    /// instead of `infer_type_cached` was an unconditional infinite loop
    /// before that was fixed) should decline, not segfault. The eager-only
    /// path (`infer_type_cached`) is unaffected: this counter only wraps
    /// the outer dispatch, exactly like `is_def_eq`'s `DEFEQ_DEPTH`.
    static INFER_DEPTH: Cell<u32> = const { Cell::new(0) };
    static DEFEQ_DEPTH: Cell<u32> = const { Cell::new(0) };
    /// Set for the duration of an "eager rescue" fallback (see
    /// `with_forced_eager_defeq`): `pub fn is_def_eq`'s NbE dispatch is
    /// a per-call decision, so a fallback that calls `is_def_eq_inner`
    /// directly at its own top level still re-enters `is_def_eq_via_nbe`
    /// as soon as `is_def_eq_core_go` recurses into a nested comparison
    /// (Pi/Lam bodies, `app_spines_congruent`'s pairwise/`defeq_args`
    /// args) — those recurse through the *dispatching* `is_def_eq`, not
    /// `is_def_eq_inner`. This flag makes the whole recursive subtree of
    /// one fallback attempt stay eager, not just its first call.
    static FORCE_EAGER_DEFEQ: Cell<bool> = const { Cell::new(false) };
    /// Set for the duration of `infer_type_via_nbe`'s own call tree (see
    /// `infer_type`). Eager never proactively reduces a Prop-major
    /// recursor application it doesn't have to: comparing `f 1 h` vs
    /// `f 1 (Acc.intro …)` succeeds via proof irrelevance on `f`'s own
    /// Prop-typed parameter *without ever unfolding `f`* (see
    /// `try_unreduced_const_congruence`'s comment). `eval` has no such
    /// laziness — it always fully reduces, so `infer_type_value`
    /// evaluating two different Lambda's domains this way can see one
    /// side's `Acc.rec` iota-reduce (major already a literal/theorem-
    /// unfolds-to-a constructor) while the other's stays opaque, landing
    /// on genuinely different normal forms (`Acc.rec … 1 …` vs
    /// `Acc.rec … 0 …`) that eager never has to reconcile because it
    /// never gets that far. `try_iota_value` checks this flag and departs
    /// from `eval`'s "always fully reduce" default specifically for
    /// Prop-major recursors (`recursor_unfolds_thm_major`'s Acc-shape
    /// check) while it's set, staying neutral instead — the same
    /// `app_arg_type_ok_eager`/`value_type_ok_eager` rescue this was
    /// already falling back to still confirms it, now by comparing
    /// *unreduced* forms that resolve via the same proof-irrelevance
    /// shortcut eager uses, instead of two already-diverged reduced ones.
    /// Never set during `is_def_eq_via_nbe`'s own comparison or plain
    /// `eval`/`is_def_eq`: those still want full iota reduction, since
    /// comparing two already-*Value*-space terms via `values_def_eq` is
    /// exactly the case where reducing both sides to the same normal form
    /// is the fast, legitimate confirmation.
    static SUPPRESS_PROP_MAJOR_ITOA: Cell<bool> = const { Cell::new(false) };
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
const CONV_DEPTH: u32 = 8_192;

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

/// Pointer-identity `Rc<nbe::Thunk>` wrapper for `iota_value_cache`'s key.
/// Unlike a bare `usize`, holding the `Rc` here keeps the thunk allocation
/// alive for as long as the cache entry does, so a later, unrelated thunk
/// can never be allocated at the same address and collide with this key.
#[derive(Clone)]
struct ThunkPtrKey(Rc<nbe::Thunk>);
impl PartialEq for ThunkPtrKey {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ThunkPtrKey {}
impl std::hash::Hash for ThunkPtrKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(state)
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
    /// `FORCE_EAGER_DEFEQ`-only namespace for the four caches directly
    /// above (see `with_forced_eager_defeq`'s comment). `is_def_eq_inner`/
    /// `infer_type_cached`/`whnf`/`whnf_core` are not invariant under
    /// `FORCE_EAGER_DEFEQ`: their own recursive calls go through the
    /// *dispatching* `is_def_eq`/`infer_type`, which take a different
    /// path (eager vs NbE) depending on the flag, so a cached answer
    /// computed one way is not generally safe to reuse computed the
    /// other way (Day 8's stale-cache bug). Rather than skip caching
    /// during a rescue entirely (Day 8; correct but wasteful — every
    /// rescue re-did all its own work from scratch, 2.7x-3.8x more
    /// `Ir` than eager on every fixture that needed one), give
    /// `FORCE_EAGER_DEFEQ`-computed answers their own cache: still pure,
    /// deterministic answers for a given `(ctx, expr)` key *as long as
    /// they were computed under the same flag*, so this is exactly as
    /// safe as the originals were before Day 8 ever introduced the
    /// bypass, just kept in a separate map so a rescue's answer can
    /// never leak into (or be leaked into by) a non-rescue lookup.
    eager_whnf_cache: RefCell<FxHashMap<(u64, usize), Expr>>,
    eager_whnf_core_cache: RefCell<FxHashMap<(u64, usize), Expr>>,
    eager_defeq_cache: RefCell<FxHashMap<(u64, usize, usize), bool>>,
    eager_infer_cache: RefCell<FxHashMap<(u64, usize), (Expr, bool)>>,
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
    /// `(rname, us, pointer-identity of params+motives+minors+major)` to
    /// the already-reduced NbE `Value` (`KIOTA_NBE=1` only). This is what
    /// lets two independently-evaluated sides that bottom out in "the same"
    /// recursor call (same closures, same literal) collapse to one shared
    /// `Rc`, so the later `Rc::ptr_eq` fast path in `values_def_eq` fires
    /// instead of re-walking a `below`-sized structure.
    ///
    /// The key holds the actual `Rc<Thunk>` clones (via `ThunkPtrKey`), not
    /// bare `usize` addresses: keying on a dropped thunk's address would
    /// let an unrelated, later thunk that the allocator reuses that address
    /// for collide with a stale entry and return a wrong (and, for a
    /// self-referential `Nat.rec` chain, non-terminating) cached value.
    /// Holding the `Rc` here keeps the address live for as long as the
    /// cache entry does.
    iota_value_cache: RefCell<FxHashMap<(u32, Vec<Level>, Vec<ThunkPtrKey>), Rc<nbe::Value>>>,
    /// Eager-path counterpart: `(rname, us, motive-ptrs, minor-ptrs, literal
    /// n) → one iota-peel result`, independent of `KIOTA_NBE`. Safe by
    /// construction (unlike the NbE cache above, the key clones the
    /// `BigUint`/`Level`s by value rather than keying on the literal's own
    /// address, and `motives`/`minors` are borrowed from `args`, which the
    /// caller keeps alive for the whole call — no dangling-pointer-reuse
    /// risk to replicate here).
    iota_lit_memo: RefCell<FxHashMap<(u32, Vec<Level>, Vec<usize>, Vec<usize>, BigUint), Expr>>,
    /// Test/diagnostic only: counts `iota_lit_memo` misses (i.e. actual
    /// `iota_from_first_principles` derivations of a Nat-literal peel).
    iota_lit_memo_misses: std::cell::Cell<u32>,
    /// Test-only override for whether `iota_lit_memo` is consulted, so a
    /// test can disable it on *this* `Checker` without mutating the
    /// process-wide `KIOTA_NO_IOTA_MEMO` env var (which `cargo test`'s
    /// parallel test threads would otherwise race on).
    iota_memo_override: std::cell::Cell<Option<bool>>,
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
    /// The constant whose own declaration is being checked right now. Real
    /// Lean's kernel adds a declaration to the environment only once it has
    /// accepted it, so a declaration's type and value are checked against an
    /// environment that does not yet contain it, and a reference to the
    /// declaration's own name inside either is an unresolved identifier. The
    /// export format cannot express recursion anyway (Lean compiles it to
    /// recursors or well-founded fixpoints), so a value that does refer to
    /// its own name is asserting itself: `theorem selfProof : ∀ p, p :=
    /// selfProof`. This checker instead inserts each declaration into
    /// `self.env` before `check_decl` runs (so the rest of a mutual block
    /// can be built), so `infer_const`/`unfold_def` hide the one constant
    /// under check for the duration of its own check — an O(1) check on
    /// every constant lookup, in contrast to a one-shot recursive scan of
    /// the whole declaration value for the name, which revisits every
    /// shared subterm of a hash-consed DAG and can blow up on a proof term
    /// with heavy sharing.
    declaring: std::cell::Cell<Option<u32>>,
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

/// Shift every parameter expression recorded in the positivity checker's
/// nested-functor `visiting` list by `by`, so entries captured at one de
/// Bruijn context depth stay meaningful after more binders are pushed (see
/// `check_arg_positive_in` / `check_specialized_ctor_positive`).
fn shift_visiting(visiting: &[(u32, Vec<Expr>)], by: i32) -> Vec<(u32, Vec<Expr>)> {
    if by == 0 {
        return visiting.to_vec();
    }
    visiting
        .iter()
        .map(|(n, ps)| (*n, ps.iter().map(|p| expr::shift(p, by, 0)).collect()))
        .collect()
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
            eager_whnf_cache: RefCell::new(FxHashMap::default()),
            eager_whnf_core_cache: RefCell::new(FxHashMap::default()),
            eager_defeq_cache: RefCell::new(FxHashMap::default()),
            eager_infer_cache: RefCell::new(FxHashMap::default()),
            infer_cache: RefCell::new(FxHashMap::default()),
            proof_arg_cache: RefCell::new(FxHashMap::default()),
            unfold_cache: RefCell::new(FxHashMap::default()),
            iota_value_cache: RefCell::new(FxHashMap::default()),
            iota_lit_memo: RefCell::new(FxHashMap::default()),
            iota_lit_memo_misses: std::cell::Cell::new(0),
            iota_memo_override: std::cell::Cell::new(None),
            fuel_nat_peels: std::cell::Cell::new(0),
            fuel_nat_last: std::cell::RefCell::new(None),
            infer_only: std::cell::Cell::new(false),
            decl_value_size: std::cell::Cell::new(0),
            checking_prop_structure: std::cell::Cell::new(false),
            eq_side_def_size: std::cell::Cell::new(0),
            checking_simple_prop_inductive: std::cell::Cell::new(false),
            eq_related_defs: RefCell::new(Vec::new()),
            eq_arg_heads: RefCell::new(Vec::new()),
            declaring: std::cell::Cell::new(None),
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
        // `ctx_key`s (via `CTX_NEXT`, reset above) are reused across
        // declarations, so a stale eager-namespace entry from the last
        // declaration would be keyed identically but mean something
        // different here.
        self.eager_whnf_cache.borrow_mut().clear();
        self.eager_whnf_core_cache.borrow_mut().clear();
        self.eager_defeq_cache.borrow_mut().clear();
        self.eager_infer_cache.borrow_mut().clear();
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
        // Only reached for axiom/def/theorem/opaque (see `check_last`'s
        // callers), none of which Lean lets mention themselves; the parser
        // has already inserted this one into `self.env` so the rest of a
        // mutual block can be built, so hide it again for the duration of
        // its own check (`infer_const`/`unfold_def`).
        self.declaring.set(Some(name));
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
            if !self.is_def_eq(&ctx, &vt, typ)? && !self.value_type_ok_eager(&ctx, value, typ)? {
                if std::env::var_os("KIOTA_DEBUG").is_some() {
                    let eager_vt = self
                        .infer_type_cached(&ctx, value)
                        .map(|t| self.pp_budget(&t, 40))
                        .unwrap_or_else(|e| format!("<eager infer failed: {e:?}>"));
                    return reject(format!(
                        "{kind} {name}: value type does not match declared type\n  got:      {}\n  expected: {}\n  got_whnf: {}\n  exp_whnf: {}\n  eager_vt: {}",
                        self.pp_budget(&vt, 40),
                        self.pp_budget(typ, 40),
                        self.pp_budget(&self.whnf(&ctx, &vt).unwrap_or_else(|_| vt.clone()), 40),
                        self.pp_budget(&self.whnf(&ctx, typ).unwrap_or_else(|_| typ.clone()), 40),
                        eager_vt,
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
            let Some(unfolded) = self.unfold_delta(*n, us, true)? else {
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

    // History: Day 5 wired `infer_type` behind `KIOTA_NBE=1` and found two
    // accept fixtures (`alg-conv-trans-acc-left`, `subject-reduction-redex`)
    // newly rejecting, and reverted. Day 6 fixed the hypothesized cause
    // (context reconstruction by quoting), but the fixtures still failed,
    // tracing down to the *actual* cause: eager reduces `Acc.rec motive
    // minor x (Acc.intro x g)` via ordinary iota, and `try_iota_value`
    // couldn't match that (`Acc` is indexed and `Acc.intro`'s recursive
    // field is higher-order). Day 7 implemented that rule and re-wired,
    // but both fixtures still rejected — a *different*, smaller mismatch:
    // eager's own comparison never re-derives an `Acc.rec`-headed type at
    // all, because it succeeds by comparing an *unreduced* wrapper
    // application (`f 1 h` vs `f 1 (Acc.intro …)`) via proof irrelevance
    // on the wrapper's Prop-typed parameter, without ever unfolding the
    // wrapper. `infer_type_value`'s `App` case, by contrast, calls `eval`
    // — which always fully reduces, unfolding the wrapper and then
    // iota-reducing its `Acc.rec` — so it can see an asymmetric "peel"
    // (one side's major stayed opaque, the other's was already a literal
    // constructor) that eager never reaches.
    //
    // `app_arg_type_ok_eager`/`value_type_ok_eager` (see their own
    // comments) close that gap: when the Value-native comparison doesn't
    // confirm, re-derive both sides' types the fully eager way and
    // compare those instead, matching eager's own judgment exactly. Two
    // more bugs had to be fixed before that rescue was actually eager end
    // to end — see `FORCE_EAGER_DEFEQ`'s comment (`is_def_eq`'s own
    // dispatch not respecting it once it recursed into a Pi/Lam body) and
    // `infer_type`'s own dispatch check just below (it checked only
    // `nbe::nbe_enabled()`, so `infer_type_uncached`'s recursive calls
    // kept re-entering `infer_type_via_nbe`) — plus gating
    // `defeq_cache`/`infer_cache`/`whnf_cache`/`whnf_core_cache` by the
    // same flag, so a rescue can't read a stale, non-forced entry (or
    // vice versa) for the same key. With all of that, both fixtures
    // accept and the wire stays: `check_decl`'s `is_def_eq(&ctx,&vt,typ)`
    // and `infer_type_value`'s own App-argument check now fall back to
    // the eager rescue rather than rejecting outright.
    pub fn infer_type(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        crate::stats::infer_call();
        // `FORCE_EAGER_DEFEQ` also gates `infer_type`'s own dispatch, not
        // just `is_def_eq`'s (see `with_forced_eager_defeq`'s comment):
        // `infer_type_uncached`'s own recursive calls (App's `f`/`a`, Lam's
        // body, …) go through this same dispatching `infer_type`, not
        // `infer_type_cached` directly, so without this an "eager rescue"
        // started via `infer_type_cached` at its own top level would still
        // re-enter `infer_type_via_nbe` for every sub-expression.
        if !nbe::nbe_enabled() || FORCE_EAGER_DEFEQ.with(Cell::get) {
            return self.infer_type_cached(ctx, e);
        }
        let depth = INFER_DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        if depth > CONV_DEPTH {
            INFER_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            return decline("infer_type depth limit");
        }
        let r = self.infer_type_via_nbe(ctx, e);
        INFER_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        r
    }

    fn infer_type_cached(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        // Closed → 0. Open `loose = k` → k innermost binders, not the full
        // telescope: a 34k DAG with one loose bvar must not re-Check under
        // every extra PSigma/Acc motive (`._unary` well-founded proofs).
        let ctx_key = ctx.term_ctx_key(e);
        let key = (ctx_key, Self::ptr_key(e));
        let infer_only = self.infer_only.get();
        // `FORCE_EAGER_DEFEQ` ("eager rescue", see `with_forced_eager_defeq`)
        // reads and writes its own namespaced cache (`eager_infer_cache`):
        // a sub-expression's type here may differ depending on whether one
        // of *its own* App-argument checks (line ~1693's `is_def_eq`)
        // re-dispatched into NbE, which can reject where eager alone
        // wouldn't (the same over-reduction `app_arg_type_ok_eager`'s own
        // comment describes). Namespacing means a rescue still benefits
        // from caching its own (and later rescues') repeated work, without
        // ever reading or writing the non-forced cache.
        let force_eager = FORCE_EAGER_DEFEQ.with(Cell::get);
        let cache_ref = if force_eager {
            &self.eager_infer_cache
        } else {
            &self.infer_cache
        };
        if let Some((t, checked)) = cache_ref.borrow().get(&key) {
            if infer_only || *checked {
                crate::stats::infer_hit();
                return Ok(t.clone());
            }
        }
        let t = self.infer_type_uncached(ctx, e)?;
        let checked = !self.infer_only.get();
        {
            let mut cache = cache_ref.borrow_mut();
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
        if self.declaring.get() == Some(n) {
            return reject(format!(
                "`{}` refers to itself; it is not in the environment until it is checked",
                self.name_str(n)
            ));
        }
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
        // Every field's own type, substituting each earlier field with
        // its own `proj sname i v` term as we walk the telescope — needed
        // for *every* field (not only up to `idx`) to check the
        // "dependent data field" rule below across the whole structure.
        let mut doms: Vec<Expr> = Vec::with_capacity(num_fields as usize);
        let mut cur = ct;
        for i in 0..num_fields {
            let (_, dom, body) = self.ensure_pi(ctx, &cur)?;
            doms.push(dom.clone());
            let proj_i = expr::proj(sname, i, v.clone());
            cur = expr::instantiate1(&body, &proj_i);
        }
        if self.is_prop(ctx, &vtw)? {
            // Lean's kernel rejects a projection out of a Prop-valued,
            // single-constructor structure unless (a) the projected
            // field is itself provably Prop at this instantiation, and
            // (b) no *earlier* field is a "dependent data field": a
            // field that is itself data (not Prop) and is referenced by
            // some field's own type, anywhere in the telescope — not
            // only by fields up to `idx`. Once such a field exists,
            // extracting anything after it in the telescope is unsound
            // (proof irrelevance forbids recovering that data field's
            // value), even for a later field whose own type never
            // mentions it (`094_projProp6`/`097_projMaybePropPast`:
            // rejected purely for coming after `someMoreData`/`field`,
            // not for using it). `091_projProp3`/`096_projMaybeProp`:
            // a data field that *isn't* referenced by anything later is
            // "non-dependent" and does not block subsequent projections.
            if !self.is_prop(ctx, &doms[idx as usize])? {
                return reject("cannot project a Type field from a Prop structure");
            }
            let mut referenced = Vec::new();
            for dom_k in &doms {
                Self::collect_proj_indices(dom_k, sname, v, &mut referenced);
            }
            let mut dependent_data_bound: Option<u32> = None;
            for j in referenced {
                if (j as usize) < doms.len()
                    && !self.is_prop(ctx, &doms[j as usize])?
                    && dependent_data_bound.is_none_or(|m| j < m)
                {
                    dependent_data_bound = Some(j);
                }
            }
            if let Some(m) = dependent_data_bound {
                if idx >= m {
                    return reject(
                        "cannot project a Prop field that comes after a dependent data field",
                    );
                }
            }
        }
        Ok(doms[idx as usize].clone())
    }

    /// Collects every `i` such that `proj sname i v` occurs as a subterm
    /// of `e` (matching `v` by pointer identity, since every occurrence
    /// built by `infer_proj`'s own substitution loop clones the same
    /// `Rc`). Used to find which earlier fields a later field's type
    /// actually mentions.
    fn collect_proj_indices(e: &Expr, sname: u32, v: &Expr, out: &mut Vec<u32>) {
        match &***e {
            ExprData::Proj(s, i, inner) if *s == sname && Rc::ptr_eq(inner, v) => out.push(*i),
            ExprData::Proj(_, _, inner) => Self::collect_proj_indices(inner, sname, v, out),
            ExprData::App(f, a) => {
                Self::collect_proj_indices(f, sname, v, out);
                Self::collect_proj_indices(a, sname, v, out);
            }
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                Self::collect_proj_indices(t, sname, v, out);
                Self::collect_proj_indices(b, sname, v, out);
            }
            ExprData::Let(t, val, b) => {
                Self::collect_proj_indices(t, sname, v, out);
                Self::collect_proj_indices(val, sname, v, out);
                Self::collect_proj_indices(b, sname, v, out);
            }
            _ => {}
        }
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
    ) -> R<Option<(u32, u32, Vec<Expr>, Vec<Level>)>> {
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
                    "IOTA to_ctor skip Prop structure ty={}",
                    self.pp_budget(&mtw, 10)
                );
            }
            return Ok(None);
        }
        let (thead, targs) = expr::unfold_apps(&mtw);
        // `all[0]` is only the right structure name for a non-mutual
        // recursor (`all.len() == 1`): a nested-recursor group member
        // stuck on a neutral major of some *other* group member's type
        // (e.g. `Cedar.Spec.Value.rec_5`'s major typed `Prod Attr Value`,
        // inside a `Value`/`List Value`/… six-way group) is a real,
        // reachable case — `Cedar.Spec.Value._sizeOf_5_eq`'s "cons" proof
        // supplies exactly this: a `head_ih` computed via the specialized
        // recursor applied to an abstract `head : Prod Attr Value`, which
        // needs struct eta on `head` itself (not on `all[0]`, `Value`)
        // before ι can fire on it at all. Reading `tname` off the major's
        // own inferred type — rather than assuming it's `all[0]` — makes
        // this work the same way for every group member, mutual or not,
        // and for a group member that is only *nested inside* `all`, not
        // one of `all`'s own listed types.
        let (tname, tus) = match &**thead {
            ExprData::Const(n, us) => (*n, (**us).clone()),
            _ => return Ok(None),
        };
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
        let _ = (params, all);
        // `tus` — the struct's own universe args, read off `major`'s own
        // (already correctly-typed) WHNF'd type head — not the *outer*
        // recursor's `us`. A nested/reused structure (`Cedar.Data.Map`'s
        // own `{u, v}`) can have a different level-parameter arity than
        // whatever recursor is eta-expanding it here (`CedarType.rec_1`'s
        // own single motive-universe `us`); zipping the constructor's
        // `level_params` against the wrong-arity `us` (the caller's
        // previous default) leaves every level past `us.len()`
        // unsubstituted — silently keeping the constructor's own raw,
        // never-instantiated declared parameter name in the eta-expanded
        // major's type, which then fails to `is_def_eq` against any
        // properly-instantiated occurrence of that same nested type
        // elsewhere in the same proof.
        Ok(Some((cname, num_params, ctor_args, tus)))
    }

    /// Whether `ty` is a proposition (`ty : Prop`), not whether `ty` *is* Prop.
    /// `whnf(Prop) = Sort 0` so a Sort is a universe (`Prop : Type`); PI must
    /// not identify `True` with `False`. Prop inductives, axioms `P : Prop`,
    /// and Pis into those count. Reads the constant's telescope, not `infer_type`
    /// of `ty` (that re-entered Check of huge type spines from PI).
    fn is_prop(&self, ctx: &Ctx, ty: &Expr) -> R<bool> {
        let w = match self.whnf(ctx, ty) {
            Ok(w) => w,
            Err(_) => return Ok(false),
        };
        match &**w {
            ExprData::Sort(_) => Ok(false),
            ExprData::BVar(i) => {
                let Some(t) = local_ty(ctx, *i) else {
                    return Ok(false);
                };
                let tw = match self.whnf(ctx, &t) {
                    Ok(x) => x,
                    Err(_) => return Ok(false),
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
                let ExprData::Const(n, _) = &**h else {
                    return self.is_prop_by_infer(ctx, &w);
                };
                // Fast paths below check the *generic*, uninstantiated
                // declared kind (`InductiveType.typ`/`const_typ`), not the
                // one with `us` (this specific use's universe arguments)
                // substituted in. That is only ever safe as a *positive*
                // test: a codomain that is *literally* `Sort 0` in the
                // generic kind (e.g. `Eq`/`False`, whose own sort never
                // depends on their level params at all) really is Prop at
                // every instantiation. A codomain that's a bare level
                // *parameter* (`PUnit.{u} : Sort u`) is not "not Prop" —
                // it's simply not decided by this untouched check; whether
                // it's Prop depends on what `u` is at *this* use
                // (`PUnit.{0}` is Prop, `PUnit.{1}` is not), which only
                // `is_prop_by_infer` (via `infer_const`'s real level
                // substitution) can answer. Treating the generic check's
                // `false` as the final answer produced a false reject on
                // *every* Prop-valued instantiation of a level-polymorphic
                // codomain (`089_projProp1`/`091_projProp3`: projecting a
                // `PUnit.{0}` field out of a Prop structure, rejected as
                // "not Prop" because the *un*instantiated `PUnit.{u}`
                // isn't literally `Sort 0`).
                if let Some(ConstantInfo::InductiveType {
                    typ, num_params, ..
                }) = self.env.get(*n)
                {
                    if (args.len() as u32) >= *num_params && self.sort_codomain_is_prop(typ) {
                        return Ok(true);
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
        self.with_infer_only(|| {
            match self.infer_type(ctx, ty) {
                Ok(s) => match self.ensure_sort(ctx, &s) {
                    Ok(l) => Ok(level::is_def_eq(&l, &level::zero())),
                    Err(_) => Ok(false),
                },
                Err(_) => Ok(false),
            }
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

    /// `App(f, App(f, App(f, ..., base)))`-shaped comparison where `f` is
    /// a *bound variable* repeated at every layer (e.g. a Church-numeral-
    /// style repeated application of a `fun`'s own parameter, nested in
    /// argument position, not spine position — `unfold_apps`'s own
    /// flattening only helps when several arguments are applied to *one*
    /// function call; it does nothing when the nesting is one single-
    /// argument application inside the next one's argument).
    ///
    /// Peels one application layer at a time from `a` and `b`
    /// simultaneously and compares each layer's own `f` with a single,
    /// immediately-completed `is_def_eq` call, so `DEFEQ_DEPTH` never
    /// accumulates past whatever depth this function's own caller is
    /// already at, no matter how many layers there are — as opposed to
    /// the normal recursive comparison, which nests one more `is_def_eq`
    /// frame (and one more `DEFEQ_DEPTH` count) per layer and hits
    /// `CONV_DEPTH` on a long enough chain even though every layer
    /// genuinely does match.
    ///
    /// Deliberately restricted to a bound-variable `f`: this peeling is
    /// only sound when "`f x` defeq `f y`" is exactly equivalent to
    /// "`x` defeq `y`", which holds for a neutral, uninterpreted
    /// variable (there is no reduction rule to invoke on it, so
    /// congruence is the *only* way two applications of it can ever be
    /// equal) but not in general for a concrete, defined function —
    /// `Int.natAbs (Int.negSucc n)` and `Int.natAbs (Int.ofNat (n+1))`
    /// are both defeq to `n+1` (`Int.natAbs` is not injective) even
    /// though `Int.negSucc n` and `Int.ofNat (n+1)` are themselves not
    /// defeq at all. An earlier version of this function recursed on
    /// the *arguments* of any matched `f`, defined constants included,
    /// once at least one layer had matched; for `Int.natAbs_neg` in
    /// Lean's own `Init` that produced exactly this false reject,
    /// comparing `Int.negSucc n` against `Int.ofNat (n+1)` directly
    /// instead of comparing `Int.natAbs` applied to each and letting the
    /// normal delta-unfold retry (below, in the caller) resolve it.
    ///
    /// Returns `None` (not applicable, caller falls back to the normal
    /// recursive path) when there is nothing to peel, the peeled `f` is
    /// not a bound variable, or the two sides' chains disagree (different
    /// length or a mismatched `f`) partway through — in the disagreement
    /// case the fallback is exactly as correct as this fast path (every
    /// layer's `f` is checked with the same `is_def_eq` either way), just
    /// potentially depth-limited, which only affects a very long
    /// *rejecting* comparison, not an accepting one: this function only
    /// ever *confirms* `Some(true)` after verifying every single layer,
    /// never `Some(true)` on a mismatch it didn't check.
    fn iterated_app_congruent(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<Option<bool>> {
        let mut cur_a = a.clone();
        let mut cur_b = b.clone();
        let mut peeled = 0u32;
        loop {
            let (fa, aa) = match &**cur_a {
                ExprData::App(f, arg) => (f.clone(), arg.clone()),
                _ => break,
            };
            let (fb, ab) = match &**cur_b {
                ExprData::App(f, arg) => (f.clone(), arg.clone()),
                _ => break,
            };
            if !matches!(&**fa, ExprData::BVar(_)) {
                break;
            }
            if !self.is_def_eq(ctx, &fa, &fb)? {
                // `fa`/`fb` themselves disagree — but `cur_a`/`cur_b`
                // (the *whole*, not-yet-peeled current layer) may still
                // be equal for a reason this per-layer `f`-vs-`f`
                // comparison can't see: `fa` might be a partial
                // application (e.g. one Church numeral partially
                // applied to another, `(n X s)`) that itself needs
                // *whnf*, not structural comparison, to reach the same
                // shape as `fb`. If we've already peeled at least one
                // matching (bound-variable) layer, recurse into
                // `is_def_eq(cur_a, cur_b)` for the remainder: that
                // re-enters the normal dispatch, which `whnf`s both
                // sides again (expanding `fa` further) before retrying —
                // genuinely making progress (`cur_a`/`cur_b` are
                // strictly smaller than the original `a`/`b`), not
                // re-asking the same question. Sound here specifically
                // because every already-peeled layer's own `f` was a
                // bound variable (see the doc comment above): congruence
                // on those was the only way they could ever be equal, so
                // reducing to "is the remainder equal" loses no
                // information. If nothing has been peeled yet, `cur_a`
                // *is* `a` — recursing here would ask the identical
                // question and loop forever, so fall back to the
                // caller's own (recursive, but not infinite)
                // `app_spines_congruent` instead.
                if peeled == 0 {
                    return Ok(None);
                }
                return Ok(Some(self.is_def_eq(ctx, &cur_a, &cur_b)?));
            }
            cur_a = aa;
            cur_b = ab;
            peeled += 1;
        }
        if peeled == 0 {
            return Ok(None);
        }
        Ok(Some(self.is_def_eq(ctx, &cur_a, &cur_b)?))
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
        let trace = std::env::var_os("KIOTA_TRACE_DEFEQ_ARGS").is_some();
        let mut ty = fn_ty.clone();
        let mut i = 0;
        while i < a1.len() {
            let (_, dom, body) = match self.ensure_pi(ctx, &ty) {
                Ok(t) => t,
                Err(e) => {
                    if trace {
                        eprintln!("DEFEQ_ARGS ensure_pi failed at i={i}: {e:?} ty={}", self.pp_budget(&ty, 60));
                    }
                    while i < a1.len() {
                        if !self.is_def_eq(ctx, &a1[i], &a2[i])? {
                            return Ok(false);
                        }
                        i += 1;
                    }
                    return Ok(true);
                }
            };
            let pi = self.domain_is_prop_inductive(ctx, &dom)?;
            let ip = self.is_prop(ctx, &dom).unwrap_or(false);
            if trace {
                eprintln!(
                    "DEFEQ_ARGS i={i} dom={} prop_inductive={pi} is_prop={ip} a1={} a2={}",
                    self.pp_budget(&dom, 40),
                    self.pp_budget(&a1[i], 30),
                    self.pp_budget(&a2[i], 30),
                );
            }
            if pi || ip {
                ty = expr::instantiate1(&body, &a1[i]);
                i += 1;
                continue;
            }
            if !self.is_def_eq(ctx, &a1[i], &a2[i])? {
                if trace {
                    eprintln!("DEFEQ_ARGS i={i} is_def_eq FAILED");
                }
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
        // See `is_def_eq_inner`'s `force_eager` comment: `whnf_core` → iota
        // → `mk_rec_call` calls the *dispatching* `is_def_eq`, so a WHNF
        // computed while NOT forced-eager can differ from one computed
        // while forced-eager. Read/write the namespaced cache instead of
        // the normal one so a rescue still benefits from memoization.
        let force_eager = FORCE_EAGER_DEFEQ.with(Cell::get);
        if let Some(r) = self.whnf_cache_get(force_eager, &k) {
            return Ok(r);
        }
        let mut cur = e.clone();
        let r = loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            if let ExprData::Const(n, us) = &**head {
                if self.eager_whnf_unfolds(*n) {
                    if let Some(unfolded) = self.unfold_delta(*n, us, true)? {
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
            if Self::is_whnf_core_redex(&r) {
                return decline(format!(
                    "WHNF core depth limit: {}",
                    self.pp_budget(&r, 12)
                ));
            }
            return Ok(r);
        }
        self.whnf_cache_insert(force_eager, k, r.clone());
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

    /// Recursive Prop inductive: theorem wrappers of the major
    /// (`_proof_2 := Acc.intro`) must unfold before iota.
    ///
    /// Day 9: `try_iota_value` (Day 7) now also drives this same gate
    /// (both eager `whnf_major` and the Value-space bridge call it), and
    /// its own ctor/iota handling is no longer restricted to Acc's exact
    /// shape (indexed + higher-order recursion both work generically now).
    /// Tried dropping the `ctors.len() == 1` restriction (any recursive
    /// Prop inductive, any constructor count) and ran the full suite both
    /// flags plus a callgrind comparison on the three Acc-shape export
    /// fixtures: no regression, no measurable instruction-count change.
    /// Left in place that pass out of caution (labeled it
    /// "soundness-adjacent" with "zero evidence of need").
    ///
    /// Day 15: dropped for real. Re-examined why: unfolding a theorem is
    /// always a valid reduction step (delta on a theorem is no different
    /// in kind from delta on a def) — this function only decides *which*
    /// recursor majors get an extra unfold-and-retry attempt before iota
    /// gives up, not whether unfolding itself is legal. A narrower ctor
    /// count can only ever *decline* to try an unfold that would have
    /// succeeded (an eager-bound completeness gap for a
    /// multi-constructor recursive Prop inductive's theorem-wrapped
    /// major), not accept something wrongly — declining is a `Decline`
    /// outcome (deferred to eager/quit), never a false accept. Both
    /// eager `whnf_major` and NBE's `try_iota_value` bridge still call
    /// this identical function, so the widening is symmetric across both
    /// flags by construction, not a new eager/NBE asymmetry.
    fn recursor_unfolds_thm_major(&self, recursor: u32) -> bool {
        let Some(ConstantInfo::Recursor { all, .. }) = self.env.get(recursor) else {
            return false;
        };
        let Some(&ind) = all.first() else {
            return false;
        };
        match self.env.get(ind) {
            Some(ConstantInfo::InductiveType { typ, is_rec, .. }) => {
                *is_rec && self.sort_codomain_is_prop(typ)
            }
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
    /// is already core-WHNF.
    fn is_whnf_core_redex(e: &Expr) -> bool {
        match &***e {
            ExprData::Let(_, _, _) => true,
            ExprData::Proj(_, _, _) => true,
            ExprData::App(_, _) => {
                let (head, _) = expr::unfold_apps(e);
                matches!(
                    &**head,
                    ExprData::Lam(_, _, _) | ExprData::Let(_, _, _) | ExprData::Proj(_, _, _)
                )
            }
            _ => false,
        }
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
            // Do not cache. A β/ζ/proj redex at the cap is not WHNF — Decline.
            // A stuck recursor/axiom app is already WHNF; returning it as Ok
            // is honest (Init `Int8.toInt_toInt32`).
            if std::env::var_os("KIOTA_TRACE_IOTA").is_some()
                || std::env::var_os("KIOTA_TRACE_EQ").is_some()
            {
                eprintln!("CORE_DEPTH abort {}", crate::expr::loose_bvar_range(&e));
            }
            if Self::is_whnf_core_redex(&e) {
                return decline(format!(
                    "WHNF core depth limit: {}",
                    self.pp_budget(&e, 12)
                ));
            }
            return Ok(e);
        }
        let k = Self::whnf_cache_key(ctx, &e);
        // See `whnf`'s `force_eager` comment just above it.
        let force_eager = FORCE_EAGER_DEFEQ.with(Cell::get);
        if let Some(r) = self.whnf_core_cache_get(force_eager, &k) {
            CORE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
            return Ok(r);
        }
        let r = self.whnf_core_go(ctx, &e);
        CORE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        let r = r?;
        self.whnf_core_cache_insert(force_eager, k, r.clone());
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
                                crate::stats::n_nat();
                                cur = r;
                                continue;
                            }
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
    fn try_unfold_const_head(&self, e: &Expr) -> R<Option<Expr>> {
        let (h, args) = expr::unfold_apps(e);
        let ExprData::Const(n, us) = &**h else {
            return Ok(None);
        };
        Ok(self.unfold_def(*n, us)?.map(|u| expr::apps(u, &args)))
    }

    fn unfold_def(&self, n: u32, us: &[Level]) -> R<Option<Expr>> {
        if self.declaring.get() == Some(n) {
            return Ok(None);
        }
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
    /// Instantiating a huge same-head body to discover that is wasted work
    /// *if it doesn't help* — but real Lean's own kernel has no size cap
    /// on same-head delta or on which theorems `is_delta` treats as
    /// reducible at all; it always tries the unfold when a comparison
    /// needs it. A cap here can only ever cost completeness (declining to
    /// try an unfold that would have succeeded), never soundness (trying
    /// an unfold that shouldn't have been tried is just wasted work, not
    /// a wrong answer — unfolding a definition is always a valid
    /// reduction step).
    ///
    /// Day 9 raised this to 1_000_000 and found `large_regular_def_unfolds_in_whnf`
    /// failing — but that test's own assertion is `!delta_body_is_small(2)`
    /// for a synthetic body, used only to demonstrate "Regular-Def WHNF
    /// unfolding is not size-gated" by picking a body definitely over
    /// *whatever* this cap currently is; it does not assert the cap's
    /// value itself is load-bearing. Day 15: lifted for real (no cap at
    /// all) and grew that test's synthetic body so it still demonstrates
    /// the same point against an uncapped `delta_body_is_small`.
    fn delta_body_is_small(&self, _n: u32) -> bool {
        true
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
        // Lean `is_delta` = `has_value`, theorems included — the real
        // kernel does not distinguish a "hot" WHNF loop from a "cold"
        // delta path at all (see `unfold_delta`'s own doc comment).
        // Nested `Syntax.rec_k` ι is rule-ctor identity +
        // specialization-order rec_group, not a size band.
        //
        // Day 9 tried widening this function alone (to
        // `Theorem { .. } => self.delta_body_is_small(n)`) and found it
        // inert: true, but only because every one of this function's own
        // call sites paired it with `unfold_def`, which — unlike
        // `unfold_delta` — never returns a `Theorem`'s value at all
        // regardless of what this function answers. That is not "safe
        // to lift", it is "provably a no-op": the widened branch was
        // dead code by construction, not evidence the eager-bound gate
        // and the correctness of unfolding are decoupled.
        //
        // Day 15: paired this widening with its call sites switching
        // from `unfold_def` to `unfold_delta(.., true)` (which already
        // implements exactly this theorem-and-size-cap rule for the
        // lazy delta path in `is_def_eq`) so the widening is no longer
        // inert. `delta_body_is_small`'s cap is still the size bound;
        // this only removes the *separate*, undocumented-as-soundness
        // restriction that the hot loop specifically excludes theorems
        // regardless of size.
        //
        // Day 17: `ConstantInfo::Def { hints: Opaque, .. }` also
        // unconditionally unfolds now, for the same reason. This variant
        // is a `def` with a `hints` *reducibility* annotation of
        // `opaque` — it still has a real, checked value (the export's
        // `"defnDecl"`/`"def"` kind) — and is a completely different
        // thing from `ConstantInfo::Opaque` (the export's separate
        // `"opaqueDecl"`/`"opaque"` kind, an axiom-with-a-witness that
        // genuinely has no kernel value to unfold). `hints` only ever
        // affects the *elaborator*'s unification/transparency strategy
        // (which definition to try first, or not to try at all when
        // `@[irreducible]`); the kernel's own `is_delta`/`whnf` do not
        // consult it at all — confirmed against the arena's own test
        // generator (`good_def`/`bad_def` in Tutorial/Meta.lean
        // unconditionally sets `hints := .opaque` on every generated
        // `def`, then runs `good` outcomes through the *real* Lean
        // kernel; `006_betaReduction`, `007_betaReduction2`, and
        // `055_reduceCtorParam.mk`/`123_reduceCtorParamRefl.mk`/
        // `124_reduceCtorParamRefl2.mk` all only type-check because the
        // kernel unfolds an opaque-*hinted* `constType`/`id`). Excluding
        // it here made every one of those `good_def`s reject with "value
        // type does not match declared type" (the `def`/`theorem`
        // couldn't be beta/delta-reduced enough to see the two sides
        // matched) or, for the positivity-checked inductives, "occurrence
        // of inductive type in unsupported position" (`positivity_whnf`
        // couldn't unfold `constType (...)` far enough to see the
        // recursive occurrence was the whole field, not a negative one).
        match self.env.get(n) {
            Some(ConstantInfo::Def { .. }) => true,
            Some(ConstantInfo::Theorem { .. }) => {
                std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_none() && self.delta_body_is_small(n)
            }
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
        let is_def = matches!(
            self.env.get(n),
            Some(ConstantInfo::Def {
                hints: ReducibilityHints::Abbrev | ReducibilityHints::Regular(_),
                ..
            })
        );
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
        let r = if nbe::nbe_enabled() && !FORCE_EAGER_DEFEQ.with(Cell::get) {
            self.is_def_eq_via_nbe(ctx, a, b)
        } else {
            self.is_def_eq_inner(ctx, a, b)
        };
        DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        r
    }

    /// Run `f` with the whole recursive `is_def_eq` call tree forced onto
    /// the eager path (see `FORCE_EAGER_DEFEQ`). Used only by
    /// `app_arg_type_ok_eager`/`value_type_ok_eager` to make an "eager
    /// rescue" attempt actually eager end to end, not just at its own
    /// top-level call.
    fn with_forced_eager_defeq<T>(&self, f: impl FnOnce() -> T) -> T {
        let prev = FORCE_EAGER_DEFEQ.with(|c| c.replace(true));
        let r = f();
        FORCE_EAGER_DEFEQ.with(|c| c.set(prev));
        r
    }

    /// Route a cache read/write to the `FORCE_EAGER_DEFEQ`-namespaced map
    /// or the normal one (see the field comment above `eager_whnf_cache`).
    fn defeq_cache_get(&self, force_eager: bool, key: &(u64, usize, usize)) -> Option<bool> {
        if force_eager {
            self.eager_defeq_cache.borrow().get(key).copied()
        } else {
            self.defeq_cache.borrow().get(key).copied()
        }
    }
    fn defeq_cache_insert(&self, force_eager: bool, key: (u64, usize, usize), v: bool) {
        if force_eager {
            self.eager_defeq_cache.borrow_mut().insert(key, v);
        } else {
            self.defeq_cache.borrow_mut().insert(key, v);
        }
    }
    fn whnf_cache_get(&self, force_eager: bool, key: &(u64, usize)) -> Option<Expr> {
        if force_eager {
            self.eager_whnf_cache.borrow().get(key).cloned()
        } else {
            self.whnf_cache.borrow().get(key).cloned()
        }
    }
    fn whnf_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {
        if force_eager {
            self.eager_whnf_cache.borrow_mut().insert(key, v);
        } else {
            self.whnf_cache.borrow_mut().insert(key, v);
        }
    }
    fn whnf_core_cache_get(&self, force_eager: bool, key: &(u64, usize)) -> Option<Expr> {
        if force_eager {
            self.eager_whnf_core_cache.borrow().get(key).cloned()
        } else {
            self.whnf_core_cache.borrow().get(key).cloned()
        }
    }
    fn whnf_core_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {
        if force_eager {
            self.eager_whnf_core_cache.borrow_mut().insert(key, v);
        } else {
            self.whnf_core_cache.borrow_mut().insert(key, v);
        }
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
        // Closed pairs → 0. Open → k innermost binders (`pair_ctx_key`).
        let ctx_key = ctx.pair_ctx_key(a, b);
        let key = (ctx_key, min_k, max_k);
        // `FORCE_EAGER_DEFEQ` ("eager rescue", see `with_forced_eager_defeq`)
        // reads and writes its own namespaced cache (`eager_defeq_cache`,
        // see the field comment above it), never the normal one: a rescue
        // computed under `FORCE_EAGER_DEFEQ` can legitimately disagree
        // with a non-forced computation for the same `(ctx, a, b)` key,
        // because `is_def_eq_via_nbe`'s own fallback can compute `false`
        // for a sub-pair that only looks unequal because `eval`
        // over-reduced one side (see `app_arg_type_ok_eager`'s comment).
        // Namespacing (rather than Day 8's skip-caching-entirely fix)
        // still lets one rescue's own repeated sub-comparisons — and later
        // rescues on the same declaration — hit a cache, while keeping
        // that answer from ever being read by, or overwritten by, a
        // non-forced lookup.
        let force_eager = FORCE_EAGER_DEFEQ.with(Cell::get);
        if let Some(r) = self.defeq_cache_get(force_eager, &key) {
            return Ok(r);
        }
        // Proof irrelevance before app congruence. Typeclass instances are
        // proofs of a Prop (the class). Pairwise of `LawfulVecOperator.mk`
        // (7 args, nested ~15 deep) is a tree walk; PI compares the inferred
        // class types instead. Acc `f 1 a` vs `f 1 (Acc.intro …)` is Bool,
        // so PI is false there and unreduced congruence still runs.
        if self.proofs_of_same_prop(ctx, a, b)? {
            self.defeq_cache_insert(force_eager, key, true);
            return Ok(true);
        }
        if self.try_unreduced_const_congruence(ctx, a, b)? {
            self.defeq_cache_insert(force_eager, key, true);
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
        if let (Ok(Some(x)), Ok(Some(y))) = (self.closed_int_value(ctx, &aw), self.closed_int_value(ctx, &bw)) {
            let r = x == y;
            self.defeq_cache_insert(force_eager, key, r);
            return Ok(r);
        }
        let r = self.is_def_eq_core(ctx, &aw, &bw)?;
        // CONV_DEPTH / CORE_DEPTH abort as Decline, not Ok(false), so a stored
        // false is a completed answer. True-only left std `#18000` retrying the
        // same failing pair — 1e9 intern hits, intern size unchanged.
        // Do not cache a result produced under a CORE_DEPTH stuck WHNF
        // (still true regardless of the eager-rescue namespace).
        if !CORE_ABORTED.with(|a| a.get()) {
            self.defeq_cache_insert(force_eager, key, r);
        }
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
        if let Some((zero, succ)) = self.nat_ctors() {
            if let (Some(x), Some(y)) = (
                nat::numeral_value(a, zero, succ),
                nat::numeral_value(b, zero, succ),
            ) {
                return Ok(x == y);
            }
        }
        // Structural match without delta.
        match (&***a, &***b) {
            (ExprData::Let(_, v, body), _) => {
                return self.is_def_eq(ctx, &expr::instantiate1(body, v), b);
            }
            (_, ExprData::Let(_, v, body)) => {
                return self.is_def_eq(ctx, a, &expr::instantiate1(body, v));
            }
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
                if let Some(r) = self.iterated_app_congruent(ctx, a, b)? {
                    return Ok(r);
                }
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
        let (cname, num_params, num_fields) = match &**ha {
            ExprData::Const(n, _) => match self.env.get(*n) {
                Some(ConstantInfo::Constructor {
                    induct,
                    num_params,
                    num_fields,
                    ..
                }) => (*induct, *num_params, *num_fields),
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
        // `a` must be the *fully* applied constructor (params and all
        // fields) — a partial application like `ULift.up Bool` (still
        // missing its `down` field) has function type, not the structure
        // type, and eta for structures does not apply to it at all: an
        // earlier version of this check derived the field count as
        // `argsa.len() - num_params` instead of reading the constructor's
        // own declared field count, so an under-applied `a` was silently
        // treated as if it had zero fields (vacuously "equal" to any `b`
        // of the same inductive head), which is unsound.
        let total_arity = num_params as usize + num_fields as usize;
        if argsa.len() != total_arity {
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

        // Recursor-application memo: a `Nat.rec`/`brecOn` "below" step
        // recurs with the *same* (motive, minors) pointers and a strictly
        // decreasing literal major. Confirm that empirically first
        // (`KIOTA_TRACE_IOTA_TRIPLES`), then skip re-deriving the ctor
        // lookup / `ctor_minor_index` / `iota_from_first_principles` /
        // `mk_rec_call` chain for a triple already seen.
        let iota_memo_on = self
            .iota_memo_override
            .get()
            .unwrap_or_else(|| std::env::var_os("KIOTA_NO_IOTA_MEMO").is_none());
        if rest.is_empty() {
            if let ExprData::Lit(Lit::Nat(n)) = &**major_w {
                if std::env::var_os("KIOTA_TRACE_IOTA_TRIPLES").is_some() {
                    eprintln!(
                        "IOTA_TRIPLE rec={} motives={:?} minors={:?} n={}",
                        self.name_str(rname),
                        motives.iter().map(Self::ptr_key).collect::<Vec<_>>(),
                        minors.iter().map(Self::ptr_key).collect::<Vec<_>>(),
                        n
                    );
                }
                if iota_memo_on {
                    let key = Self::iota_lit_memo_key(rname, &us, motives, minors, n);
                    if let Some(cached) = self.iota_lit_memo.borrow().get(&key) {
                        crate::stats::n_nat();
                        return Ok(Some(cached.clone()));
                    }
                }
            }
        }
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
            ExprData::Const(cname, ctor_us) => match self.env.get(*cname) {
                Some(ConstantInfo::Constructor {
                    induct,
                    num_params: cnp,
                    ..
                }) if all.contains(induct) || rec_owns_ctor(*cname) => {
                    Some((*cname, *cnp, margs.clone(), Some((**ctor_us).clone())))
                }
                _ => None,
            },
            ExprData::Lit(Lit::Nat(n)) => {
                if let Some((zero, succ)) = self.nat_ctors() {
                    let nat_induct = match self.env.get(zero) {
                        Some(ConstantInfo::Constructor { induct, .. }) => Some(*induct),
                        _ => None,
                    };
                    if nat_induct.map(|ind| all.contains(&ind)).unwrap_or(false) || rec_owns_ctor(zero) {
                        if n == &num_bigint::BigUint::from(0u32) {
                            Some((zero, 0, vec![], None))
                        } else if n.bits() > 256 {
                            // Lean `LEAN_NAT_MAX_SIZE`-style byte cap, not a
                            // bits∈[20,24] fingerprint of hugeFuel vs 2^32.
                            return decline("Nat literal exceeds byte cap");
                        } else {
                            // One succ peel per iota (C++ natLit). WHNF-core
                            // may continue; uniform WHNF_DEPTH declines.
                            let pred = n - 1u32;
                            Some((succ, 0, vec![expr::lit_nat(pred)], None))
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

        let (cname, cnp, ctor_args, ctor_us) = if let Some(x) = ctor {
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
            (x.0, x.1, x.2, Some(x.3))
        } else if k_like {
            match self.k_like_ctor(ctx, &all, params, major)? {
                Some(x) => (x.0, x.1, x.2, None),
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

        let minor_idx = self
            .minor_index_from_type(rname, &us, &level_params, params, cname, ctor_params)
            .unwrap_or_else(|| self.ctor_minor_index(cname, rname, &all));
        if minor_idx >= minors.len() {
            return Ok(None);
        }
        if matches!(&**major_w, ExprData::Lit(Lit::Nat(_))) {
            self.iota_lit_memo_misses.set(self.iota_lit_memo_misses.get() + 1);
        }
        // The constructor's own universe args at the application site
        // (`ctor_us`) — not `us` (the *outer* recursor's own levels).
        // For a nested/reused type (`Cedar.Data.Map.mk`'s `{u1, u2}`
        // inside a group whose own shared levels are just `{u2'}`, say),
        // substituting the ctor's declared level params with `us`
        // mismatches in length/identity, leaving some of the ctor's own
        // level params entirely unsubstituted — a free `u60`-style
        // leftover that then compares unequal to the same nested type's
        // properly-instantiated form elsewhere in the same proof
        // (`Cedar.Spec.Value._sizeOf_3_eq`: this left the "cons" case's
        // generated IH pointing at the *wrong* group member, since the
        // wrong-leveled major type no longer matched any candidate's own
        // declared major and fell through to the name-only fallback).
        // Falls back to `us` only when the ctor's own application-site
        // levels aren't available (the literal-major and structure/K
        // shortcuts above, none of which build a group member's own
        // multi-level-param constructor the way a literal `Const` major
        // does).
        let ctor_us_owned = ctor_us.unwrap_or_else(|| us.to_vec());
        let rhs = self.iota_from_first_principles(
            ctx,
            rname,
            &us,
            &ctor_us_owned,
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
        if iota_memo_on && rest.is_empty() {
            if let ExprData::Lit(Lit::Nat(n)) = &**major_w {
                let key = Self::iota_lit_memo_key(rname, &us, motives, minors, n);
                self.iota_lit_memo.borrow_mut().insert(key, rhs.clone());
            }
        }
        Ok(Some(expr::apps(rhs, rest)))
    }

    /// Test/diagnostic accessor for `iota_lit_memo_misses`.
    pub(crate) fn iota_lit_memo_miss_count(&self) -> u32 {
        self.iota_lit_memo_misses.get()
    }

    /// Test-only: force `iota_lit_memo` on/off for this `Checker` instance,
    /// bypassing `KIOTA_NO_IOTA_MEMO` (see `iota_memo_override`).
    #[cfg(test)]
    pub(crate) fn set_iota_memo_enabled_for_test(&self, on: bool) {
        self.iota_memo_override.set(Some(on));
    }

    fn iota_lit_memo_key(
        rname: u32,
        us: &[Level],
        motives: &[Expr],
        minors: &[Expr],
        n: &BigUint,
    ) -> (u32, Vec<Level>, Vec<usize>, Vec<usize>, BigUint) {
        (
            rname,
            us.to_vec(),
            motives.iter().map(Self::ptr_key).collect(),
            minors.iter().map(Self::ptr_key).collect(),
            n.clone(),
        )
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

    /// Find the group member specialized for the exact nested type
    /// `target target_args..` (e.g. `List Value` vs `List (Prod String
    /// Value)`), by checking each candidate's own declared major-premise
    /// type — not `nested_rec_for`'s constructor-name search, which
    /// cannot tell two specializations of the same polymorphic type
    /// apart (`List.nil`/`List.cons` are the same constants regardless of
    /// element type, so a group with two different `List` specializations
    /// has two members whose rules both name them; the first-match search
    /// always picks whichever is sorted first, not the one whose own
    /// major premise is actually `target target_args..`). Same shape and
    /// same reasoning as `minor_index_from_type`, for recursor identity
    /// instead of minor-slot identity. Returns `None` (falls back to
    /// `nested_rec_for`) for any shape this doesn't handle cleanly.
    fn nested_rec_for_type(
        &self,
        ctx: &Ctx,
        rname: u32,
        us: &[Level],
        params: &[Expr],
        target: u32,
        target_args: &[Expr],
    ) -> Option<u32> {
        for rec in self.rec_group(rname) {
            let (typ, rec_level_params, rec_num_params, num_motives, num_minors, num_indices) =
                match self.env.get(rec) {
                    Some(ConstantInfo::Recursor {
                        typ,
                        level_params,
                        num_params,
                        num_motives,
                        num_minors,
                        num_indices,
                        ..
                    }) => (
                        typ.clone(),
                        level_params.clone(),
                        *num_params,
                        *num_motives,
                        *num_minors,
                        *num_indices,
                    ),
                    _ => continue,
                };
            if rec_level_params.len() != us.len() || rec_num_params as usize != params.len() {
                continue;
            }
            let subst = level::subst_map(&rec_level_params, us);
            let typ = expr::instantiate_level_params(&typ, &subst);
            let params_rev: Vec<Expr> = params.iter().rev().cloned().collect();
            let mut cur = expr::instantiate(&typ, &params_rev);
            let mut ok = true;
            for _ in 0..(rec_num_params + num_motives + num_minors + num_indices) {
                match &**cur {
                    ExprData::Pi(_, _, body) => cur = body.clone(),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let major_dom = match &**cur {
                ExprData::Pi(_, dom, _) => dom.clone(),
                _ => continue,
            };
            let (mh, margs) = expr::unfold_apps(&major_dom);
            if let ExprData::Const(c, _) = &**mh {
                if *c == target && margs.len() >= target_args.len() {
                    // Structural `==` is too strict here: two occurrences
                    // of the *same* nested type can carry differently
                    // *named* (but defeq) universe level arguments —
                    // e.g. one path substitutes a group's own concrete
                    // levels, another leaves a generic level parameter
                    // from a shared instance's own declaration in place.
                    // A false decline here (from `!=` on an otherwise-
                    // identical type) is what let `nested_rec_for`'s
                    // ambiguous, name-only fallback silently pick the
                    // wrong group member (`Cedar.Spec.Value._sizeOf_3_eq`:
                    // `List Value`'s `rec_3`, sorted first, instead of
                    // `List (Prod Attr Value)`'s `rec_4`, both owning
                    // `List.cons`/`List.nil`).
                    let matches = margs[..target_args.len()]
                        .iter()
                        .zip(target_args)
                        .all(|(a, b)| a == b || self.is_def_eq(ctx, a, b).unwrap_or(false));
                    if matches {
                        return Some(rec);
                    }
                }
            }
        }
        None
    }

    /// Find `cname`'s minor-premise slot directly from `rname`'s own type
    /// signature, instead of a heuristic count over the group's sort
    /// order (`ctor_minor_index`). A nested-recursor group shares one
    /// global minor numbering across every member (`minors.len()` is the
    /// same for `rec`, `rec_1`, …), and each minor's own declared type is
    /// `Π (fields/IHs...), motive_j (C params.. fields..)` — a shape that
    /// names its constructor `C` and that constructor's own params
    /// directly, with no ambiguity, regardless of how many *other*
    /// specializations in the group happen to reuse the same constructor
    /// name for a different element type (`List.cons` is one constant
    /// shared by every `List _` instantiation, so a six-way mutual group
    /// with two different `List` specializations has two separate
    /// `List.nil`/`List.cons`-shaped minors at two different slots).
    /// Matching on the constructor's own params (not just its name) is
    /// what tells those two slots apart, and does so from the type
    /// signature alone — no dependence on `self.rec_group`'s own sort
    /// order at all. Returns `None` (falls back to the heuristic) for any
    /// shape this doesn't handle cleanly, e.g. an indexed recursor whose
    /// conclusion isn't a single-argument `motive major`, or if the type
    /// doesn't parse as expected — never a wrong answer, just a decline
    /// to the existing behavior.
    ///
    /// On `Cedar.Spec.Value._sizeOf_5_eq`'s own two-same-shaped-`List`
    /// group, this independently derives the same slot `ctor_minor_index`
    /// already did post-fix: the group's sort order was not, in fact, the
    /// source of that reject (verified, not assumed — both approaches
    /// agree here). The remaining gap there is a different one: the
    /// generated `head_ih` for a nested-recursor field mutually typed
    /// with the group (e.g. `Prod`) is a *specialized* recursor
    /// application (`rec_5` here), while the proof compares it against a
    /// *generic* typeclass-instance application for the same field
    /// (`SizeOf.sizeOf` routed through `Prod`'s own, non-specialized
    /// recursor) — both stuck on the same neutral variable, needing
    /// "these are two different recursors for the same type, with
    /// pointwise-equal motives/minors" as its own defeq principle, which
    /// this checker does not implement. Out of scope for this pass.
    fn minor_index_from_type(
        &self,
        rname: u32,
        us: &[Level],
        rec_level_params: &[u32],
        params: &[Expr],
        cname: u32,
        ctor_params: &[Expr],
    ) -> Option<usize> {
        let (typ, rec_num_params, num_motives, num_minors) = match self.env.get(rname) {
            Some(ConstantInfo::Recursor {
                typ,
                num_params,
                num_motives,
                num_minors,
                ..
            }) => (typ.clone(), *num_params, *num_motives, *num_minors),
            _ => return None,
        };
        if rec_level_params.len() != us.len() || rec_num_params as usize != params.len() {
            return None;
        }
        let subst = level::subst_map(rec_level_params, us);
        let typ = expr::instantiate_level_params(&typ, &subst);
        // `params` is in application order (outermost/first-bound first);
        // `instantiate` substitutes bvar 0 (innermost) with `args[0]`, so
        // reverse before threading them through the leading `Pi`s.
        let params_rev: Vec<Expr> = params.iter().rev().cloned().collect();
        let mut cur = expr::instantiate(&typ, &params_rev);
        for _ in 0..(rec_num_params + num_motives) {
            match &**cur {
                ExprData::Pi(_, _, body) => cur = body.clone(),
                _ => return None,
            }
        }
        for p in 0..num_minors {
            let (mut inner, next) = match &**cur {
                ExprData::Pi(_, dom, body) => (dom.clone(), body.clone()),
                _ => return None,
            };
            loop {
                match &**inner {
                    ExprData::Pi(_, _, body) => inner = body.clone(),
                    _ => break,
                }
            }
            let (_motive, concl_args) = expr::unfold_apps(&inner);
            if let Some(major_shape) = concl_args.last() {
                let (chead, cargs) = expr::unfold_apps(major_shape);
                if let ExprData::Const(c, _) = &**chead {
                    if *c == cname
                        && cargs.len() >= ctor_params.len()
                        && cargs[..ctor_params.len()] == *ctor_params
                    {
                        return Some(p as usize);
                    }
                }
            }
            cur = next;
        }
        None
    }

    fn ctor_minor_index(&self, cname: u32, rname: u32, all: &[u32]) -> usize {
        // `rname`'s own position for `cname` first: a nested group's own
        // constructor can be *polymorphic* (`List.cons` is the same
        // constant regardless of its element type), so two different
        // specializations in the same group (`List Value`'s recursor and
        // `List (Prod Attr Value)`'s, say) can each list a rule for the
        // exact same `cname`. Matching the first occurrence across the
        // *whole* group, regardless of which recursor is actually being
        // reduced, silently picked whichever specialization's rule (and
        // RHS) happened to come first in the group's order — the wrong
        // one whenever `rname` itself isn't that first specialization.
        // This fixes that misattribution (never uses a *different*
        // recursor's rule for the constructor being reduced), but the
        // offset added below still assumes `self.rec_group`'s own sort
        // order lines up with the actual, shared minor-slot layout the
        // group's individual definitions (e.g. a mutual `sizeOf` helper)
        // were built against; a group with more than one same-shaped
        // nested specialization (two `List.nil`/`List.cons` pairs, for
        // distinct element types, both in one group) can still combine
        // with the wrong minor if that assumption doesn't hold for a
        // given export. Confirmed independently correct — and needed —
        // for every existing fixture (the `Acc`/`PersistentHashMap.Node`
        // nested-recursor cases): only known to be incomplete on a case
        // pulled from the live `cedar` export with two same-shaped `List`
        // specializations in one six-way mutual group.
        let mut idx = 0usize;
        for rec in self.rec_group(rname) {
            let rules = match self.env.get(rec) {
                Some(ConstantInfo::Recursor { rules, .. }) => rules,
                _ => continue,
            };
            if rec == rname {
                if let Some(local) = rules.iter().position(|r| r.ctor == cname) {
                    return idx + local;
                }
            }
            idx += rules.len();
        }
        // Fallback for a `cname` `rname` doesn't own directly (shouldn't
        // normally happen: `try_iota`'s own ctor detection already
        // requires `rec_owns_ctor(cname)` or `all.contains(induct)` before
        // calling here) — first match by ctor name anywhere in the group.
        idx = 0;
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
        ctor_us: &[Level],
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
        // `ctor_us`, the constructor's own universe args at its
        // application site — not `us` (see the call site's own comment).
        let subst = level::subst_map(&ctor_lp, ctor_us);
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
            (
                rec,
                iargs[..nparams].to_vec(),
                &iargs[nparams..],
            )
        } else if let Some(nrec) = self.nested_rec_for_type(&tctx, rname, us, params, target, &iargs) {
            // `nested_rec_for_type` matches on `ty`'s own head and args
            // against each candidate's *actual declared major-premise
            // type* — sound regardless of whether `occurs_any` (below)
            // can see the recursion at all. `occurs_any` is a purely
            // syntactic check for the group's own type *name* appearing
            // literally inside `ty`; it correctly catches direct nesting
            // (`List Value` inside `Value`'s own group) but misses
            // *indirect* nesting through some other, independently-named
            // type in between (`Cedar.Validation.CedarType`'s own
            // `List (Prod Attr QualifiedType)` field: `QualifiedType`
            // itself wraps `CedarType`, but the literal name `CedarType`
            // never appears in `List (Prod Attr QualifiedType)`, so
            // `occurs_any` said "not recursive" and this field's own
            // induction hypothesis was silently dropped — under-applying
            // a `below`-shaped minor by exactly that many argument slots
            // and leaving it stuck as a bare, unapplied `Ctor.mk`-minor
            // lambda instead of a fully-reduced value, which is what
            // `Cedar.SymCC.TermType.ofType`'s own `.fst`/`.snd`
            // projections out of that stuck lambda then reject on).
            (nrec, params.iter().map(|p| expr::shift(p, shift_by, 0)).collect(), &[][..])
        } else if self.occurs_any(&ty, all) {
            // Fallback for a shape `nested_rec_for_type` doesn't parse
            // cleanly: the older, name-only search, unchanged.
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
            ExprData::Const(n, _) => {
                let s = self.name_str(*n);
                s == "Int" || s.ends_with(".Int")
            }
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

    fn is_closed_numeral(l: &Level) -> bool {
        match &**l {
            crate::level::LevelData::Zero => true,
            crate::level::LevelData::Succ(a) => Self::is_closed_numeral(a),
            _ => false,
        }
    }

    fn is_strict_succ_of(hi: &Level, lo: &Level) -> bool {
        let mut n = 0u32;
        let mut cur = hi.clone();
        while let crate::level::LevelData::Succ(a) = &*cur {
            n += 1;
            cur = a.clone();
        }
        n > 0 && level::is_def_eq(&cur, lo)
    }

    /// Lean kernel `elim_only_at_universe_zero` (`src/kernel/inductive.cpp`):
    /// whether the recursor(s) for the (mutual) inductive group `all` may
    /// only eliminate into `Prop` (motive codomain fixed at `Sort 0`),
    /// rather than an arbitrary `Sort u`. This is Lean's own,
    /// syntax-approximated "is this Prop a subsingleton" check — the
    /// justification for the exception is that a subsingleton has at
    /// most one proof, so a motive that can see into `Sort u` still
    /// cannot distinguish two different proofs (there's only one).
    ///
    /// Sort-u inductives are entirely unaffected — the whole notion of
    /// "elim only at 0" only makes sense for a type that could actually
    /// *be* `Prop` for some universe assignment. Checked via
    /// `level::is_not_zero` on the type's own declared sort, matching
    /// the kernel's own `m_is_not_zero` exactly (not `is_def_eq` against
    /// literal `zero`, which only catches an unconditionally-Prop type
    /// and would let a level-polymorphic predicate like `Sort u` through
    /// unrestricted for every `u`, including `u := 0`).
    ///
    /// For a possibly-Prop, non-mutual, single-constructor type, Lean's
    /// own two-part field check (case 3 below) is why a `Sort u`-valued
    /// field is only safe to expose through the motive when it already
    /// occurs literally in the constructor's own conclusion (its own
    /// index arguments): that information was never hidden — it's part
    /// of the term's declared type, not something the recursor would be
    /// leaking out of an opaque proof.
    ///
    /// Restricted (Prop-only) when any of:
    ///   1. `all.len() > 1`: mutually recursive predicates.
    ///   2. the type has more than one constructor.
    ///   3. the type has exactly one constructor with a field that is
    ///      not itself Prop-valued (case 1 below fails) *and* does not
    ///      occur in the constructor's own conclusion (case 2 fails) —
    ///      e.g. `inductive Bad : Prop | mk (x : Sort 1)`: `x`'s own
    ///      type is `Sort 1` (not Prop, `is_not_zero`), and `Bad` has no
    ///      indices at all for `x` to occur in, so a `Bad.rec` motive
    ///      that reaches `Sort 1` could pull `x` itself out of an opaque
    ///      `Bad` proof — combined with proof irrelevance (any two
    ///      `Bad.mk` proofs are equal), that proves `False`.
    /// Not restricted (large elim OK) when the type has zero
    /// constructors (e.g. `False`: vacuously fine, nothing to leak) or
    /// its one constructor's every non-Prop field occurs in the
    /// conclusion (e.g. `Eq.refl`'s `a` occurs as both of `Eq`'s own
    /// indices).
    fn elim_only_at_universe_zero(&self, all: &[u32]) -> R<bool> {
        let tname0 = all[0];
        let (num_params0, num_indices0, typ0) = match self.env.get(tname0) {
            Some(ConstantInfo::InductiveType {
                num_params,
                num_indices,
                typ,
                ..
            }) => (*num_params, *num_indices, typ.clone()),
            _ => return Ok(false),
        };
        let mut ctx0 = Ctx::new();
        let mut cur0 = typ0;
        for _ in 0..(num_params0 + num_indices0) {
            let (_, dom, body) = self.ensure_pi(&ctx0, &cur0)?;
            ctx0.push(dom);
            cur0 = body;
        }
        let result_level = self.ensure_sort(&ctx0, &cur0)?;
        if level::is_not_zero(&result_level) {
            // For every universe assignment the type is not Prop, so
            // it's not an inductive predicate at all.
            return Ok(false);
        }
        if all.len() > 1 {
            return Ok(true);
        }
        let ctors = match self.env.get(tname0) {
            Some(ConstantInfo::InductiveType { ctors, .. }) => ctors.clone(),
            _ => return Ok(false),
        };
        if ctors.len() > 1 {
            return Ok(true);
        }
        let Some(&cname) = ctors.first() else {
            // Zero constructors (`False`): vacuously large-elim OK.
            return Ok(false);
        };
        let (c_typ, c_np) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                typ, num_params, ..
            }) => (typ.clone(), *num_params),
            _ => return Ok(false),
        };
        let mut cctx = Ctx::new();
        let mut cur = c_typ;
        let mut pos: u32 = 0;
        // bvar-depth positions of fields that are not themselves Prop.
        let mut to_check: Vec<u32> = Vec::new();
        loop {
            match &**cur {
                ExprData::Pi(_, dom, body) => {
                    if pos >= c_np {
                        if let Ok(ds) = self.infer_type(&cctx, dom) {
                            if let Ok(field_lvl) = self.ensure_sort(&cctx, &ds) {
                                if level::is_not_zero(&field_lvl) {
                                    to_check.push(pos);
                                }
                            }
                        }
                    }
                    cctx.push(dom.clone());
                    cur = body.clone();
                    pos += 1;
                }
                _ => break,
            }
        }
        let (_, args) = expr::unfold_apps(&cur);
        for p in &to_check {
            let expected = expr::bvar(pos - 1 - p);
            if !args.iter().any(|a| **a == *expected) {
                return Ok(true);
            }
        }
        Ok(false)
    }

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
                                let too_big_closed = Self::is_closed_numeral(&field_lvl)
                                    && Self::is_closed_numeral(&t_sort)
                                    && !level::leq(&field_lvl, &t_sort, 0);
                                let too_big_succ = Self::is_strict_succ_of(&field_lvl, &t_sort);
                                if (too_big_closed || too_big_succ)
                                    && !level::is_def_eq(&t_sort, &level::zero())
                                {
                                    return reject(
                                        "constructor field universe is too big for the inductive type",
                                    );
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
        // Large-elimination check, once per group (not once per member —
        // `check_inductive_group` runs once per type name in the block,
        // all sharing the same `all`). See `elim_only_at_universe_zero`'s
        // own comment for the exact rule being enforced.
        if all.first() == Some(&first_name) && self.elim_only_at_universe_zero(&all)? {
            let mut recs: Vec<u32> = all
                .iter()
                .filter_map(|t| self.env.rec_of.get(t).copied())
                .collect();
            recs.sort_unstable();
            recs.dedup();
            for rname in recs {
                let (r_typ, r_np, r_nm) = match self.env.get(rname) {
                    Some(ConstantInfo::Recursor {
                        typ,
                        num_params,
                        num_motives,
                        ..
                    }) => (typ.clone(), *num_params, *num_motives),
                    _ => continue,
                };
                let mut mctx = Ctx::new();
                let mut cur = r_typ;
                for _ in 0..r_np {
                    let (_, dom, body) = self.ensure_pi(&mctx, &cur)?;
                    mctx.push(dom);
                    cur = body;
                }
                for _ in 0..r_nm {
                    let (_, dom, body) = self.ensure_pi(&mctx, &cur)?;
                    let motive_ok = {
                        let mut mtctx = mctx.clone();
                        let mut mt = dom.clone();
                        loop {
                            match self.ensure_pi(&mtctx, &mt) {
                                Ok((_, d, b)) => {
                                    mtctx.push(d);
                                    mt = b;
                                }
                                Err(_) => break,
                            }
                        }
                        self.ensure_sort(&mtctx, &mt)
                            .is_ok_and(|l| level::is_def_eq(&l, &level::zero()))
                    };
                    if !motive_ok {
                        return reject(format!(
                            "recursor `{}` allows large elimination out of a Prop-valued inductive that is not a subsingleton",
                            self.name_str(rname)
                        ));
                    }
                    mctx.push(dom);
                    cur = body;
                }
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
        match self.whnf(ctx, e) {
            Ok(w) => Ok(w),
            Err(TcError::Decline(m)) => Err(TcError::Decline(m)),
            Err(_) => reject("cannot prove constructor argument is positive"),
        }
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
        let mut peeled = 0i32;
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
                    peeled += 1;
                }
                _ => break,
            }
        }
        // `visiting` records, per outer nested-functor call, the parameter
        // expressions the cycle check (`params_defeq`, called from
        // `check_nested_functor`) later compares fresh occurrences against
        // — but those recorded expressions are only meaningful relative to
        // the de Bruijn context depth they were captured at. Every `Pi`
        // peeled above pushes one more binder onto `ctx2` without this
        // constructor argument's own binders being reflected in
        // `visiting`'s stored expressions, so a later occurrence found
        // under those same binders is compared, via `is_def_eq` at the
        // *new*, deeper `ctx2`, against params that still sit at the
        // *old*, shallower depth: never equal, no matter how many times
        // the exact same nested type/params pair recurs. Shifting
        // `visiting`'s contents by the same amount keeps them meaningful
        // at `ctx2`'s depth, so a genuine repeat is recognized and the
        // cycle check (which is the only thing bounding this recursion)
        // actually bounds it.
        let visiting_shifted = shift_visiting(visiting, peeled);
        self.check_positive_spine(&ctx2, &cur, bound, num_params, &visiting_shifted)
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
    ///
    /// Day 9: checked whether this repo has a "nested positivity depth
    /// 16"-style cap that could now be replaced with a functor-identity
    /// cycle check. It doesn't — there's no depth counter anywhere in the
    /// positivity checker (`check_positivity`/`check_arg_positive_in`/
    /// `check_specialized_ctor_positive` all take no depth parameter).
    /// The only bound on nested-functor recursion is `visiting` below:
    /// exact `(name, params)` identity, via `params_defeq`, which *is*
    /// already the functor-identity check the candidate asked for, not a
    /// raw depth cap standing in for one. Nothing to lift here; this is
    /// inductive-declaration checking (`check_inductive_group`), not
    /// `is_def_eq`/`infer_type`, so it was out of this pass's scope
    /// either way.
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
        // Each field after the first sits one more binder deep than the
        // last (`ctx2.push(dom)` below, once per preceding field), same
        // reasoning as `check_arg_positive_in`'s own shift: `visiting`'s
        // recorded params are only meaningful at the context depth they
        // were captured at, so they need to be shifted to stay meaningful
        // for a later field's own occurrence check.
        let mut visiting_cur = visiting.to_vec();
        loop {
            match &**cur {
                ExprData::Pi(_, dom, body) => {
                    self.check_arg_positive_in(&ctx2, dom, bound, i_num_params, &visiting_cur)?;
                    ctx2.push(dom.clone());
                    visiting_cur = shift_visiting(&visiting_cur, 1);
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

    // ---------------- NbE spike (`KIOTA_NBE=1`, `is_def_eq` only) ----------------
    //
    // See `nbe.rs` for the design rationale. Everything below only ever
    // asserts `Ok(true)` when it can justify it structurally (two values
    // reduced, via legitimate reduction steps, to a matching canonical or
    // neutral shape); anything else — mismatch, or a construct this spike
    // does not model — is surfaced as `Ok(false)`/`Err` and the caller
    // (`is_def_eq_via_nbe`) falls back to the eager comparator for a
    // definitive answer. NbE can only accelerate a `true` it would reach
    // anyway; it never overrides the eager verdict.

    pub(crate) fn is_def_eq_via_nbe(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        let depth = ctx.len() as u32;
        let attempt: R<bool> = (|| {
            let env = crate::nbe::generic_env(depth);
            let va = self.eval(&env, a)?;
            let vb = self.eval(&env, b)?;
            self.values_def_eq(depth, &va, &vb)
        })();
        match attempt {
            Ok(true) => Ok(true),
            _ => self.is_def_eq_inner(ctx, a, b),
        }
    }

    pub(crate) fn eval(&self, env: &nbe::VEnv, e: &Expr) -> R<Rc<nbe::Value>> {
        crate::stats::whnf_call();
        match &***e {
            ExprData::BVar(i) => {
                let idx = env
                    .len()
                    .checked_sub(1 + *i as usize)
                    .ok_or_else(|| TcError::Other("nbe: bvar out of range".into()))?;
                env[idx].force(self)
            }
            ExprData::Sort(l) => Ok(Rc::new(nbe::Value::Sort(l.clone()))),
            ExprData::Lit(l) => Ok(Rc::new(nbe::Value::Lit(l.clone()))),
            ExprData::Lam(bi, ty, body) => {
                let dom = nbe::Thunk::deferred(env.clone(), ty.clone());
                Ok(Rc::new(nbe::Value::Lam(*bi, dom, env.clone(), body.clone())))
            }
            ExprData::Pi(bi, ty, body) => {
                let dom = nbe::Thunk::deferred(env.clone(), ty.clone());
                Ok(Rc::new(nbe::Value::Pi(*bi, dom, env.clone(), body.clone())))
            }
            ExprData::Let(_ty, val, body) => {
                let mut env2 = (**env).clone();
                env2.push(nbe::Thunk::deferred(env.clone(), val.clone()));
                self.eval(&Rc::new(env2), body)
            }
            ExprData::Proj(s, i, v) => {
                let vv = self.eval(env, v)?;
                self.eval_proj(*s, *i, vv)
            }
            ExprData::Const(n, us) => self.eval_const(*n, us),
            ExprData::App(f, a) => {
                let vf = self.eval(env, f)?;
                let arg = nbe::Thunk::deferred(env.clone(), a.clone());
                self.apply(vf, arg, env.len() as u32)
            }
        }
    }

    fn eval_const(&self, n: u32, us: &Rc<Vec<Level>>) -> R<Rc<nbe::Value>> {
        if self.eager_whnf_unfolds(n) {
            if let Some(body) = self.unfold_delta(n, us, true)? {
                return self.eval(&nbe::empty_env(), &body);
            }
        }
        Ok(Rc::new(nbe::Value::Neutral(nbe::Neutral::Const(n, us.clone()))))
    }

    fn eval_proj(&self, sname: u32, idx: u32, v: Rc<nbe::Value>) -> R<Rc<nbe::Value>> {
        if let nbe::Value::Neutral(nv) = &*v {
            let (chead, cargs) = Self::unwind_neutral(nv);
            if let nbe::Neutral::Const(cname, _) = chead {
                if let Some(ConstantInfo::Constructor {
                    num_params,
                    induct,
                    ..
                }) = self.env.get(*cname)
                {
                    if *induct == sname {
                        let fi = (*num_params + idx) as usize;
                        if let Some(f) = cargs.get(fi) {
                            return f.force(self);
                        }
                    }
                }
            }
        }
        Ok(Rc::new(nbe::Value::Neutral(nbe::Neutral::Proj(
            sname,
            idx,
            Rc::new(match &*v {
                nbe::Value::Neutral(nv) => Self::clone_neutral(nv),
                _ => return decline("nbe: proj of a non-structure value"),
            }),
        ))))
    }

    fn clone_neutral(n: &nbe::Neutral) -> nbe::Neutral {
        match n {
            nbe::Neutral::Var(l) => nbe::Neutral::Var(*l),
            nbe::Neutral::Const(a, us) => nbe::Neutral::Const(*a, us.clone()),
            nbe::Neutral::App(f, a) => nbe::Neutral::App(Rc::new(Self::clone_neutral(f)), a.clone()),
            nbe::Neutral::Proj(s, i, v) => nbe::Neutral::Proj(*s, *i, Rc::new(Self::clone_neutral(v))),
        }
    }

    /// Unwind a `Neutral` spine into `(root, args)`, args in application
    /// order (first-applied first) — the `Value`-space analogue of
    /// `expr::unfold_apps`.
    fn unwind_neutral(n: &nbe::Neutral) -> (&nbe::Neutral, Vec<Rc<nbe::Thunk>>) {
        let mut args = Vec::new();
        let mut cur = n;
        loop {
            match cur {
                nbe::Neutral::App(f, a) => {
                    args.push(a.clone());
                    cur = f;
                }
                _ => break,
            }
        }
        args.reverse();
        (cur, args)
    }

    pub(crate) fn apply(
        &self,
        vf: Rc<nbe::Value>,
        arg: Rc<nbe::Thunk>,
        depth: u32,
    ) -> R<Rc<nbe::Value>> {
        match &*vf {
            nbe::Value::Lam(_, _, env, body) => {
                let mut env2 = (**env).clone();
                env2.push(arg);
                self.eval(&Rc::new(env2), body)
            }
            nbe::Value::Neutral(n) => self.apply_neutral(n, arg, depth),
            _ => decline("nbe: apply to a non-function value"),
        }
    }

    fn apply_neutral(
        &self,
        n: &nbe::Neutral,
        arg: Rc<nbe::Thunk>,
        depth: u32,
    ) -> R<Rc<nbe::Value>> {
        let spine = nbe::Neutral::App(Rc::new(Self::clone_neutral(n)), arg);
        if let Some(v) = self.try_iota_value(&spine, depth)? {
            return Ok(v);
        }
        Ok(Rc::new(nbe::Value::Neutral(spine)))
    }

    /// Reduce a recursor application whose major is a `Nat` literal or a
    /// fully-applied constructor of a type in `all` — `Nat.rec`/`List.rec`/
    /// `brecOn`-shaped structural recursion, indexed recursors (`Acc.rec`),
    /// and higher-order (binder-introducing) recursive occurrences
    /// (`Acc.intro`'s `∀ y, r y x → Acc r y` field) all included. Anything
    /// this can't match eager's own rule on (K-like/structure eta, nested-
    /// inductive recursion, an unresolvable major) is left neutral:
    /// `Ok(None)`, which makes the whole comparison "uncertain" and defers
    /// to eager — never a "close enough" wrong reduction.
    ///
    /// Indices are handled exactly like eager `try_iota`: skipped over
    /// (folded into `major_pos`) and never separately inspected — the
    /// checker doesn't re-validate them here any more than eager does.
    /// The "apply minor to fields, interleave one rec-call per recursive
    /// field" step (arbitrary binder count, indices threaded through a
    /// field's own occurrence type) is *not* reimplemented here: it calls
    /// eager's own `iota_from_first_principles`/`mk_rec_call` directly, on
    /// quoted params/ctor_params/motives/minors/fields, to guarantee it
    /// matches eager's rule by construction rather than by a second,
    /// independently-written (and soundness-critical) copy of it. This
    /// bridge is bounded, not accumulating: params/motives/minors are
    /// fixed for the whole reduction (never grow with recursion depth),
    /// and `fields` are this one constructor application's own (small)
    /// arguments — never the "below"/accumulator value itself, which
    /// never gets serialized: it stays purely in Value space, nested
    /// inside the *lazy* argument thunks `eval`'s own `App` case already
    /// creates for the rec-call embedded in `rhs`, so a minor that
    /// ignores its `ih` still never forces it.
    fn try_iota_value(&self, spine: &nbe::Neutral, depth: u32) -> R<Option<Rc<nbe::Value>>> {
        let (root, args) = Self::unwind_neutral(spine);
        let (rname, us) = match root {
            nbe::Neutral::Const(n, us) => (*n, us.clone()),
            _ => return Ok(None),
        };
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
        if args.len() != major_pos + 1 {
            return Ok(None);
        }
        if let Some(cached) = self.iota_value_cache(rname, &us, &args) {
            return Ok(Some(cached));
        }
        // `SUPPRESS_PROP_MAJOR_ITOA` (see its own comment): inside
        // `infer_type_via_nbe`'s call tree, a Prop-major recursor
        // (Acc-shape) declines to iota-reduce even on a ctor/theorem-
        // unfolds-to-ctor major, deferring to the eager rescue instead of
        // risking an asymmetric reduction eager itself never performs.
        // Nat.rec/List.rec/brecOn-shaped structural recursion (Nat's own
        // major type isn't Prop) is entirely unaffected.
        if SUPPRESS_PROP_MAJOR_ITOA.with(Cell::get) && self.recursor_unfolds_thm_major(rname) {
            return Ok(None);
        }
        let params = &args[..num_params as usize];
        let motives = &args[num_params as usize..(num_params + num_motives) as usize];
        let minors =
            &args[(num_params + num_motives) as usize..(num_params + num_motives + num_minors) as usize];
        let mut major_v = args[major_pos].force(self)?;

        let rec_owns_ctor = |cname: u32| -> bool {
            matches!(
                self.env.get(rname),
                Some(ConstantInfo::Recursor { rules, .. }) if rules.iter().any(|r| r.ctor == cname)
            )
        };

        // Theorem-wrapped major (`_proof := Acc.intro …`): eager unfolds
        // this via `recursor_unfolds_thm_major` + `whnf_major` before iota
        // ever sees it. Bridge to that exact mechanism — never a weaker
        // reimplementation — when native forcing didn't already land on a
        // ctor/`Nat`-literal head.
        if self.recursor_unfolds_thm_major(rname) && !self.is_ctor_or_nat_lit_value(&major_v)? {
            let major_q = self.quote(depth, &major_v)?;
            let unfolded = self.whnf_major(&Self::dummy_ctx(depth), &major_q, rname)?;
            major_v = self.eval(&nbe::generic_env(depth), &unfolded)?;
        }

        let ctor: Option<(u32, u32, Vec<Rc<nbe::Thunk>>, Option<Vec<Level>>)> = match &*major_v {
            nbe::Value::Lit(Lit::Nat(n)) => {
                let Some((zero, succ)) = self.nat_ctors() else {
                    return Ok(None);
                };
                let nat_induct = match self.env.get(zero) {
                    Some(ConstantInfo::Constructor { induct, .. }) => Some(*induct),
                    _ => None,
                };
                if !(nat_induct.map(|i| all.contains(&i)).unwrap_or(false) || rec_owns_ctor(zero)) {
                    return Ok(None);
                }
                if *n == BigUint::from(0u32) {
                    Some((zero, 0, Vec::new(), None))
                } else if n.bits() > 256 {
                    // Same byte cap as the eager path (`nat.rs`); stays
                    // neutral so the fallback keeps the eager decline.
                    return Ok(None);
                } else {
                    let pred = n - 1u32;
                    Some((
                        succ,
                        0,
                        vec![nbe::Thunk::forced(Rc::new(nbe::Value::Lit(Lit::Nat(pred))))],
                        None,
                    ))
                }
            }
            nbe::Value::Neutral(nv) => {
                let (chead, cargs) = Self::unwind_neutral(nv);
                match chead {
                    nbe::Neutral::Const(cname, ctor_us) => match self.env.get(*cname) {
                        Some(ConstantInfo::Constructor {
                            induct,
                            num_params: cnp,
                            ..
                        }) if all.contains(induct) || rec_owns_ctor(*cname) => {
                            Some((*cname, *cnp, cargs, Some((**ctor_us).clone())))
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        };
        let Some((cname, cnp, ctor_args, ctor_us)) = ctor else {
            return Ok(None);
        };
        if (ctor_args.len() as u32) < cnp {
            return Ok(None);
        }
        let ctor_params = &ctor_args[..cnp as usize];
        let fields = &ctor_args[cnp as usize..];

        let dctx = Self::dummy_ctx(depth);
        let params_q = self.quote_all(depth, params)?;
        let ctor_params_q = self.quote_all(depth, ctor_params)?;
        let motives_q = self.quote_all(depth, motives)?;
        let minors_q = self.quote_all(depth, minors)?;
        let fields_q = self.quote_all(depth, fields)?;

        let minor_idx = self
            .minor_index_from_type(rname, &us, &level_params, &params_q, cname, &ctor_params_q)
            .unwrap_or_else(|| self.ctor_minor_index(cname, rname, &all));
        if minor_idx >= minors.len() {
            return Ok(None);
        }
        // See eager's own call site comment: the ctor's own
        // application-site universe args, not `us` (the outer
        // recursor's), or a nested type's own multi-level-param
        // constructor is left partly unsubstituted.
        let ctor_us_owned = ctor_us.unwrap_or_else(|| us.to_vec());
        let rhs = self.iota_from_first_principles(
            &dctx,
            rname,
            &us,
            &ctor_us_owned,
            &level_params,
            &all,
            &params_q,
            &ctor_params_q,
            &motives_q,
            &minors_q,
            minors_q[minor_idx].clone(),
            cname,
            &fields_q,
        )?;
        let result = self.eval(&nbe::generic_env(depth), &rhs)?;
        self.iota_value_cache_insert(rname, &us, &args, result.clone());
        Ok(Some(result))
    }

    /// `Ctx` of the given depth, entries of an arbitrary but valid
    /// placeholder type (`Sort 0`) — used only to hand eager's
    /// `iota_from_first_principles`/`mk_rec_call`/`whnf_major` a `Ctx` of
    /// matching length for their own internal `ensure_pi`/`whnf`/
    /// `is_def_eq` calls on the *quoted* (bounded, non-accumulating)
    /// params/motives/minors/fields passed in alongside it. Those internal
    /// checks (e.g. `mk_rec_call`'s param-match `is_def_eq`) only ever
    /// gate whether a field counts as a recursive occurrence — a wrong
    /// answer there can only make the bridge under- rather than over-
    /// recognize a rec-call (`Ok(None)`, deferring to eager), never
    /// produce an unsound accept.
    fn dummy_ctx(depth: u32) -> Ctx {
        let mut ctx = Ctx::new();
        let placeholder = expr::sort(level::zero());
        for _ in 0..depth {
            ctx.push(placeholder.clone());
        }
        ctx
    }

    fn quote_all(&self, depth: u32, thunks: &[Rc<nbe::Thunk>]) -> R<Vec<Expr>> {
        thunks
            .iter()
            .map(|t| {
                let v = t.force(self)?;
                self.quote(depth, &v)
            })
            .collect()
    }

    /// `Value`-space analogue of `is_ctor_or_nat_lit_head`.
    fn is_ctor_or_nat_lit_value(&self, v: &nbe::Value) -> R<bool> {
        Ok(match v {
            nbe::Value::Lit(Lit::Nat(_)) => true,
            nbe::Value::Neutral(nv) => {
                let (chead, _) = Self::unwind_neutral(nv);
                matches!(
                    chead,
                    nbe::Neutral::Const(n, _)
                        if matches!(self.env.get(*n), Some(ConstantInfo::Constructor { .. }))
                )
            }
            _ => false,
        })
    }

    fn iota_value_cache_key(
        &self,
        rname: u32,
        us: &Rc<Vec<Level>>,
        args: &[Rc<nbe::Thunk>],
    ) -> (u32, Vec<Level>, Vec<ThunkPtrKey>) {
        let ptrs = args.iter().cloned().map(ThunkPtrKey).collect();
        (rname, (**us).clone(), ptrs)
    }

    fn iota_value_cache(
        &self,
        rname: u32,
        us: &Rc<Vec<Level>>,
        args: &[Rc<nbe::Thunk>],
    ) -> Option<Rc<nbe::Value>> {
        let key = self.iota_value_cache_key(rname, us, args);
        self.iota_value_cache.borrow().get(&key).cloned()
    }

    fn iota_value_cache_insert(
        &self,
        rname: u32,
        us: &Rc<Vec<Level>>,
        args: &[Rc<nbe::Thunk>],
        v: Rc<nbe::Value>,
    ) {
        let key = self.iota_value_cache_key(rname, us, args);
        self.iota_value_cache.borrow_mut().insert(key, v);
    }

    /// Convert a `Value` back to an `Expr`, for tests and error paths only —
    /// the hot `values_def_eq` comparison never needs to quote.
    pub(crate) fn quote(&self, depth: u32, v: &nbe::Value) -> R<Expr> {
        match v {
            nbe::Value::Sort(l) => Ok(expr::sort(l.clone())),
            nbe::Value::Lit(Lit::Nat(n)) => Ok(expr::lit_nat(n.clone())),
            nbe::Value::Lit(Lit::Str(s)) => Ok(expr::lit_str((**s).clone())),
            nbe::Value::Lam(bi, dom, env, body) => {
                let domv = dom.force(self)?;
                let domq = self.quote(depth, &domv)?;
                let fresh = nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(nbe::Neutral::Var(depth))));
                let mut env2 = (**env).clone();
                env2.push(fresh);
                let bodyv = self.eval(&Rc::new(env2), body)?;
                let bodyq = self.quote(depth + 1, &bodyv)?;
                Ok(expr::lam(*bi, domq, bodyq))
            }
            nbe::Value::Pi(bi, dom, env, body) => {
                let domv = dom.force(self)?;
                let domq = self.quote(depth, &domv)?;
                let fresh = nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(nbe::Neutral::Var(depth))));
                let mut env2 = (**env).clone();
                env2.push(fresh);
                let bodyv = self.eval(&Rc::new(env2), body)?;
                let bodyq = self.quote(depth + 1, &bodyv)?;
                Ok(expr::pi(*bi, domq, bodyq))
            }
            nbe::Value::Neutral(n) => self.quote_neutral(depth, n),
        }
    }

    fn quote_neutral(&self, depth: u32, n: &nbe::Neutral) -> R<Expr> {
        match n {
            nbe::Neutral::Var(level) => {
                if *level >= depth {
                    return Err(TcError::Other("nbe: level out of range during quote".into()));
                }
                Ok(expr::bvar(depth - level - 1))
            }
            nbe::Neutral::Const(name, us) => Ok(expr::const_(*name, (**us).clone())),
            nbe::Neutral::App(f, a) => {
                let fq = self.quote_neutral(depth, f)?;
                let av = a.force(self)?;
                let aq = self.quote(depth, &av)?;
                Ok(expr::app(fq, aq))
            }
            nbe::Neutral::Proj(s, i, v) => {
                let vq = self.quote_neutral(depth, v)?;
                Ok(expr::proj(*s, *i, vq))
            }
        }
    }

    /// Structural equality of two `Value`s. `Ok(true)` is a sound, final
    /// answer (matching canonical/neutral shapes are definitionally equal
    /// by construction of `eval`). `Ok(false)` means "not confirmed" —
    /// mismatch *or* an unsupported shape — and the caller must treat that
    /// as "ask eager", never as a confirmed inequality.
    pub(crate) fn values_def_eq(&self, depth: u32, va: &Rc<nbe::Value>, vb: &Rc<nbe::Value>) -> R<bool> {
        if Rc::ptr_eq(va, vb) {
            return Ok(true);
        }
        match (&**va, &**vb) {
            (nbe::Value::Sort(l1), nbe::Value::Sort(l2)) => Ok(level::is_def_eq(l1, l2)),
            (nbe::Value::Lit(x), nbe::Value::Lit(y)) => Ok(x == y),
            (nbe::Value::Neutral(n1), nbe::Value::Neutral(n2)) => self.neutral_def_eq(depth, n1, n2),
            (nbe::Value::Pi(_, d1, e1, b1), nbe::Value::Pi(_, d2, e2, b2)) => {
                let dv1 = d1.force(self)?;
                let dv2 = d2.force(self)?;
                if !self.values_def_eq(depth, &dv1, &dv2)? {
                    return Ok(false);
                }
                let fresh = nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(nbe::Neutral::Var(depth))));
                let mut env1 = (**e1).clone();
                env1.push(fresh.clone());
                let mut env2 = (**e2).clone();
                env2.push(fresh);
                let bv1 = self.eval(&Rc::new(env1), b1)?;
                let bv2 = self.eval(&Rc::new(env2), b2)?;
                self.values_def_eq(depth + 1, &bv1, &bv2)
            }
            (nbe::Value::Lam(_, d1, e1, b1), nbe::Value::Lam(_, d2, e2, b2)) => {
                let dv1 = d1.force(self)?;
                let dv2 = d2.force(self)?;
                if !self.values_def_eq(depth, &dv1, &dv2)? {
                    return Ok(false);
                }
                let fresh = nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(nbe::Neutral::Var(depth))));
                let mut env1 = (**e1).clone();
                env1.push(fresh.clone());
                let mut env2 = (**e2).clone();
                env2.push(fresh);
                let bv1 = self.eval(&Rc::new(env1), b1)?;
                let bv2 = self.eval(&Rc::new(env2), b2)?;
                self.values_def_eq(depth + 1, &bv1, &bv2)
            }
            _ => Ok(false),
        }
    }

    fn neutral_def_eq(&self, depth: u32, n1: &nbe::Neutral, n2: &nbe::Neutral) -> R<bool> {
        match (n1, n2) {
            (nbe::Neutral::Var(l1), nbe::Neutral::Var(l2)) => Ok(l1 == l2),
            (nbe::Neutral::Const(a, ua), nbe::Neutral::Const(b, ub)) => Ok(a == b
                && ua.len() == ub.len()
                && ua.iter().zip(ub.iter()).all(|(x, y)| level::is_def_eq(x, y))),
            (nbe::Neutral::App(f1, a1), nbe::Neutral::App(f2, a2)) => {
                if !self.neutral_def_eq(depth, f1, f2)? {
                    return Ok(false);
                }
                let v1 = a1.force(self)?;
                let v2 = a2.force(self)?;
                self.values_def_eq(depth, &v1, &v2)
            }
            (nbe::Neutral::Proj(s1, i1, v1), nbe::Neutral::Proj(s2, i2, v2)) => {
                Ok(s1 == s2 && i1 == i2 && self.neutral_def_eq(depth, v1, v2)?)
            }
            _ => Ok(false),
        }
    }

    // ---------------- NbE spike, Day 4/5/6: infer_type on Values ----------------
    //
    // `pub fn infer_type` (the one every other part of the checker calls)
    // is untouched: it still always returns `Expr`, exactly as before, so
    // `check_decl`'s actual type-checking path has zero behavior change
    // from anything in this section unless/until it's wired in.
    //
    // Day 5 wired this once and found a real disagreement: two accept
    // fixtures rejected under KIOTA_NBE=1, both on the same shape (a bound
    // variable vs. a theorem applied to that variable, both proofs of the
    // same Prop). The cause was `vctx_to_ctx`: every fallback point
    // rebuilt an eager `Ctx` by *quoting* each tracked `Value` type, and
    // that round trip (through `eval` once when the type was first tracked,
    // then `quote` again to reconstruct `Ctx`, then `eval` *again* inside
    // whatever eager function the fallback called — `proofs_of_same_prop`
    // calls `infer_type` on `ctx`, which under the flag re-enters this same
    // machinery) was enough to lose whatever the real, never-reconstructed
    // `Ctx` preserves that eager's proof-irrelevance/App-argument checks
    // depend on. `types_compatible` calling `is_def_eq_inner` directly
    // (bypassing `KIOTA_NBE`'s own dispatch) ruled out a dispatch loop as
    // the cause — swapping that in changed nothing, isolating the bug to
    // the reconstruction itself, not to which comparator got called.
    //
    // Day 6 fix: never reconstruct `Ctx` by quoting. `infer_type_value`
    // (and every helper below) now carries the *original* `ctx: &Ctx`
    // alongside `tys`/`env`, growing it in lockstep for `Lam`/`Pi` (which
    // eager's own `Ctx` grows for too) — and every eager fallback call
    // (`infer_type_cached`, `is_def_eq_inner`, `infer_proj`, and anything
    // eager calls transitively, e.g. `proofs_of_same_prop`) gets that real
    // `ctx` plus the *original* sub-`Expr`, never a quoted stand-in. `Let`
    // is handled the way eager's own `infer_type_uncached` already does —
    // zeta first (`expr::instantiate1(body, val)`), then infer the
    // substituted term under the *same* `ctx`/`tys`/`env`, no new level at
    // all — so there is no separate "did `ctx` grow here" bookkeeping to
    // get wrong between the two structures. `quote` is now used only where
    // it always should have been: turning a *Value-native* successful
    // result back into an `Expr` at `infer_type_via_nbe`'s own boundary
    // (and inside `types_compatible`, to hand a genuinely Value-native
    // `got`/`want` pair — with no original `Expr` at all — to eager for a
    // decisive comparison).

    fn vctx_new() -> (Vec<Rc<nbe::Thunk>>, nbe::VEnv) {
        (Vec::new(), nbe::empty_env())
    }

    /// Push a fresh (unknown-value) binder of type `ty` into all three of
    /// `ctx`/`tys`/`env` at once, as `infer_type_uncached` does for
    /// `Lam`/`Pi` (the only forms whose eager `Ctx` actually grows).
    ///
    /// `ty_thunk` is a `Thunk`, not a forced `Value` (Day 10's
    /// substitution-based redesign, see the comment above
    /// `infer_type_value`): the binder's type is not evaluated just
    /// because it was bound, only if/when some later `BVar` occurrence of
    /// it actually needs a `Value` (`infer_type_value`'s own `BVar` case
    /// forces it then, and `Thunk::force` memoizes so that costs at most
    /// once no matter how many occurrences there are).
    fn vctx_push(
        ctx: &Ctx,
        tys: &[Rc<nbe::Thunk>],
        env: &nbe::VEnv,
        ty_expr: &Expr,
        ty_thunk: Rc<nbe::Thunk>,
    ) -> (Ctx, Vec<Rc<nbe::Thunk>>, nbe::VEnv) {
        let level = env.len() as u32;
        let mut ctx2 = ctx.clone();
        ctx2.push(ty_expr.clone());
        let mut tys2 = tys.to_vec();
        tys2.push(ty_thunk);
        let mut env2 = (**env).clone();
        env2.push(nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(
            nbe::Neutral::Var(level),
        ))));
        (ctx2, tys2, Rc::new(env2))
    }

    /// `KIOTA_NBE=1` dispatch target for `pub fn infer_type`. Computes the
    /// type via `infer_type_value` (Value-native for the core calculus,
    /// falling back to `infer_type_cached` — never `infer_type`'s own
    /// dispatch again, to skip a redundant flag re-check — for anything it
    /// doesn't model) and quotes the result back to `Expr` at the
    /// declaration/call boundary this function itself is.
    ///
    /// A `Reject` from `infer_type_value` is trusted directly: every reject
    /// it can produce is either a raw structural fact (an out-of-range
    /// bvar/projection index — not a soundness judgement, the same either
    /// representation) or backed by `types_compatible`/`is_prop`, which
    /// only ever decide via the proven eager `is_def_eq`/`is_prop` — on the
    /// real `ctx`, never a reconstructed one. Any other outcome (an
    /// internal `Other`/`Decline`, or quoting failing on an otherwise-
    /// successful inference) defers to `infer_type_cached` entirely: per
    /// the contract, a bug here may cost completeness, never turn into a
    /// wrong accept.
    fn infer_type_via_nbe(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        if std::env::var_os("KIOTA_TRACE_INFER_NBE").is_some() {
            eprintln!(
                "infer_type_via_nbe ctxlen={} e={}",
                ctx.len(),
                self.pp_budget(e, 40)
            );
        }
        // `SUPPRESS_PROP_MAJOR_ITOA` (see its own comment): scoped to this
        // call's own recursive subtree, including any nested `infer_type`
        // dispatch back into `infer_type_via_nbe` for a sub-expression.
        let prev = SUPPRESS_PROP_MAJOR_ITOA.with(|c| c.replace(true));
        let r = self.infer_type_via_nbe_inner(ctx, e);
        SUPPRESS_PROP_MAJOR_ITOA.with(|c| c.set(prev));
        r
    }

    fn infer_type_via_nbe_inner(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        // Day 10 (`KIOTA_TRACE_RESCUE=1`): confirms this function's own
        // `ctx`-re-evaluation loop below is not the source of the Acc-shape
        // `Ir` cost either — on `alg-conv-trans-acc-right.accept.ndjson`
        // this runs 221 times with combined `ctx.len()` of 594, negligible
        // next to `eval`'s ~55k total calls. See `types_compatible`'s
        // comment for where the cost actually is.
        if std::env::var_os("KIOTA_TRACE_RESCUE").is_some() {
            eprintln!("INFER_VIA_NBE ctxlen={}", ctx.len());
        }
        // Day 10: `ctx[i]`'s type used to be eagerly `eval`'d here on
        // every single call — for every sub-expression `infer_type`
        // recurses into, not just once — regardless of whether that
        // binder is ever actually looked up. Deferred instead: a `BVar`
        // occurrence that's never inferred (e.g. `infer_only` skips the
        // App-argument check it would've been needed for) now never
        // forces it at all, and `Thunk::force`'s own memoization means a
        // binder referenced many times still only costs one `eval`.
        let mut tys: Vec<Rc<nbe::Thunk>> = Vec::with_capacity(ctx.len());
        let mut env = nbe::empty_env();
        for i in 0..ctx.len() {
            tys.push(nbe::Thunk::deferred(env.clone(), ctx[i].clone()));
            let level = env.len() as u32;
            let mut env2 = (*env).clone();
            env2.push(nbe::Thunk::forced(Rc::new(nbe::Value::Neutral(
                nbe::Neutral::Var(level),
            ))));
            env = Rc::new(env2);
        }
        match self.infer_type_value(ctx, &tys, &env, e) {
            Ok(tv) => self
                .quote(ctx.len() as u32, &tv)
                .or_else(|_| self.infer_type_cached(ctx, e)),
            Err(rej @ TcError::Reject(_)) => Err(rej),
            Err(_) => self.infer_type_cached(ctx, e),
        }
    }

    /// `infer_type_cached` on the *real* `ctx` and the *original* `e` —
    /// never a quoted stand-in for either. Also never `infer_type`: that
    /// re-dispatches to `infer_type_via_nbe` under `KIOTA_NBE=1`, which is
    /// *this function's own caller* — an unconditional infinite loop the
    /// instant this fallback ever fires with the flag on (confirmed by a
    /// real stack overflow before that fix; see the Day 5 PR update).
    fn infer_type_value_fallback(
        &self,
        ctx: &Ctx,
        env: &nbe::VEnv,
        e: &Expr,
    ) -> R<Rc<nbe::Value>> {
        let t = self.infer_type_cached(ctx, e)?;
        self.eval(env, &t)
    }

    /// Definitive type-compatibility check: try the fast Value-native
    /// comparison first (sound whenever it confirms `true`, per
    /// `values_def_eq`'s contract), and only when it doesn't, fall back to
    /// eager's own `is_def_eq_inner` (never `is_def_eq`'s dispatch) on the
    /// real `ctx` — quoting `got`/`want` here is unavoidable (they may be
    /// genuinely Value-native results, e.g. a `Pi` built from an inferred
    /// `Lam` body, with no original `Expr` to fall back to at all), but
    /// `ctx` itself is always the caller's real one, never reconstructed.
    fn types_compatible(
        &self,
        ctx: &Ctx,
        depth: u32,
        got: &Rc<nbe::Value>,
        want: &Rc<nbe::Value>,
    ) -> R<bool> {
        if self.values_def_eq(depth, got, want)? {
            return Ok(true);
        }
        let got_q = self.quote(depth, got)?;
        let want_q = self.quote(depth, want)?;
        // Day 10: this fallback was calling `is_def_eq_inner` directly,
        // *not* wrapped in `with_forced_eager_defeq` — a real, separate
        // gap from the two named rescues (`app_arg_type_ok_eager`/
        // `value_type_ok_eager`), now closed the same way: as soon as its
        // own recursion (Pi/Lam bodies, `app_spines_congruent`'s
        // pairwise/`defeq_args` args) went through the *dispatching*
        // `is_def_eq`, it re-entered `is_def_eq_via_nbe` for every nested
        // sub-comparison regardless of whether either named rescue ever
        // ran.
        //
        // Measured with `KIOTA_TRACE_RESCUE=1` on the three Acc-shape
        // export fixtures: `app_arg_type_ok_eager`/`value_type_ok_eager`
        // are invoked *zero* times on any of them, and forcing eager here
        // (this fix) plus the cache-namespacing and `SUPPRESS_PROP_MAJOR_
        // ITOA` fixes above changed the measured `callgrind` `Ir` by
        // noise (<1%), not the 2.7x-3.8x this session's task expected to
        // move. The actual cost, confirmed by instrumenting `eval` and
        // `infer_type_via_nbe`'s own `ctx`-re-evaluation loop separately,
        // is neither caches nor an asymmetric iota peel: it's that
        // `infer_type_value` computes types by *evaluating* — `eval`
        // always fully reduces every node it touches (Const unfolds,
        // App applies, the final `motive`-substitution step calls `eval`
        // again) — where eager's `infer_type_cached` computes the exact
        // same types by *substituting* (`expr::instantiate1`, an O(1)
        // pointer op via structural sharing/interning, no reduction at
        // all). For a large proof term (the well-founded-recursion value
        // these fixtures actually check), that is a real, structural
        // difference in how much work each strategy does per node, not a
        // missed cache or an avoidable reduction — `infer_type_via_nbe`
        // itself only runs 221 times with 594 total `ctx` entries
        // re-evaluated on the largest fixture (negligible), while `eval`
        // alone accounts for essentially all ~55k reduction-counter hits.
        // Closing this gap for real would mean `infer_type_value` (or a
        // variant of it) computing types without evaluating through them
        // — i.e. substitution-based, like eager — which is a materially
        // different design for that function, not a bounded fix; out of
        // scope for this pass. The three fixes above stay: each closes a
        // real correctness/consistency gap in the eager-rescue mechanism
        // ("a slower correct rescue is better than a wrong wire"), even
        // though none of them, individually or together, move this
        // fixture's `Ir` ratio.
        self.with_forced_eager_defeq(|| self.is_def_eq_inner(ctx, &got_q, &want_q))
    }

    /// Last-resort fallback for an App argument-type check that
    /// `types_compatible` couldn't confirm on the *evaluated* (`Value`)
    /// forms. `eval` always fully reduces (unfolds every `Def` on the
    /// spine, then tries iota) before anything gets compared, which can
    /// turn `f x y` into a `Recursor`-headed spine — and
    /// `try_unreduced_const_congruence` *deliberately* refuses to
    /// proof-irrelevance-compare Recursor spines unreduced (its own
    /// comment: "Recursor spines … must WHNF/δ/ι first"), while it
    /// happily does so for an ordinary `Def` like `f` itself. So a check
    /// that would succeed at the `f x y` level via proof irrelevance on a
    /// `Prop`-typed argument, without ever needing to unfold `f`, can
    /// still fail once `eval` has already unfolded `f` for us and only
    /// one side's `Recursor` major happened to reduce further than the
    /// other's (e.g. one side's major is a bound variable, the other a
    /// theorem that unfolds to a constructor).
    ///
    /// Eager `infer_type`/`ensure_pi` never proactively reduces (it only
    /// substitutes), so re-deriving both types the eager way and
    /// comparing them with `is_def_eq_inner` (never `is_def_eq`, which
    /// would re-dispatch into this same NbE path) reproduces exactly the
    /// comparison eager itself would have made, at the same
    /// (un-reduced) level. Only ever used to *rescue* a decline into an
    /// accept that matches eager's own judgment; any error or eager
    /// mismatch here still rejects.
    fn app_arg_type_ok_eager(&self, ctx: &Ctx, f: &Expr, a: &Expr) -> R<bool> {
        // Day 10: `KIOTA_TRACE_RESCUE=1` logs every invocation of this and
        // `value_type_ok_eager` with the term sizes involved. Used to
        // confirm (not guess) that neither one is actually invoked on the
        // Acc-shape export fixtures at all — see the comment above
        // `types_compatible`.
        if std::env::var_os("KIOTA_TRACE_RESCUE").is_some() {
            eprintln!(
                "RESCUE app f_size={} a_size={}",
                expr_size_capped(f, 100_000),
                expr_size_capped(a, 100_000)
            );
        }
        // The whole rescue — including re-deriving `f`'s and `a`'s types,
        // not just the final comparison — must stay eager: `infer_type_cached`
        // itself calls the *dispatching* `is_def_eq` for its own App-argument
        // checks (inside `f`'s or `a`'s own structure), which would otherwise
        // re-enter NbE (and risk the exact over-reduction this rescue exists
        // to route around) before this function's own comparison ever runs.
        self.with_forced_eager_defeq(|| {
            let ft = match self.infer_type_cached(ctx, f) {
                Ok(t) => t,
                Err(_) => return Ok(false),
            };
            let dom = match self.ensure_pi(ctx, &ft) {
                Ok((_, dom, _)) => dom,
                Err(_) => return Ok(false),
            };
            let at = match self.infer_type_cached(ctx, a) {
                Ok(t) => t,
                Err(_) => return Ok(false),
            };
            self.is_def_eq_inner(ctx, &at, &dom)
        })
    }

    /// `check_decl`'s counterpart to `app_arg_type_ok_eager`: when `vt`
    /// (`infer_type`'s, possibly Value-native, answer for the whole
    /// declaration value) doesn't convert with the declared `typ` under
    /// `is_def_eq` (which itself may re-dispatch into NbE and re-reduce
    /// both sides), re-derive the value's type the fully eager way —
    /// `infer_type_cached` never proactively reduces — and compare that
    /// against `typ` with `is_def_eq_inner` directly (never `is_def_eq`,
    /// to avoid re-dispatching into the same NbE path). Only ever rescues
    /// a decline into an accept that matches eager's own judgment.
    fn value_type_ok_eager(&self, ctx: &Ctx, value: &Expr, typ: &Expr) -> R<bool> {
        if std::env::var_os("KIOTA_TRACE_RESCUE").is_some() {
            eprintln!("RESCUE value value_size={}", expr_size_capped(value, 100_000));
        }
        // See `app_arg_type_ok_eager`'s comment: re-deriving `value`'s type
        // must also stay eager end to end, not just the final comparison.
        self.with_forced_eager_defeq(|| {
            let eager_vt = match self.infer_type_cached(ctx, value) {
                Ok(t) => t,
                Err(_) => return Ok(false),
            };
            self.is_def_eq_inner(ctx, &eager_vt, typ)
        })
    }

    /// `infer_type_value` mirrors eager `infer_type_uncached`'s own
    /// strategy — **substitute, don't evaluate the term being inferred**
    /// — not `eval`'s. `App`/`Lam`/`Pi`/`Let` build the result type by
    /// deferring the just-introduced binder (`Thunk::deferred`, forced
    /// only if a later `BVar` occurrence actually needs it) rather than
    /// calling `self.eval` on it up front. Only `Const`/`Lit` evaluate
    /// unconditionally, and only a small, fixed, closed type (the
    /// constant's own declared type, or `Nat`/`String`'s type) — never a
    /// subterm of the term actually being checked.
    ///
    /// Day 8 found the concrete failure mode this fixes: `eval` always
    /// fully reduces (`Def` unfolds, then tries iota), so eagerly
    /// `eval`-ing a `Lam`'s domain or an `App`'s argument as part of
    /// *inferring a type* could reduce a `Prop`-major recursor
    /// application that eager's own `infer_type`/`ensure_pi` never
    /// touches at all (eager only substitutes). Comparing two
    /// independently-`eval`'d domains that happened to iota-reduce by
    /// different amounts (one major stayed opaque, the other was already
    /// a literal/theorem-unfolds-to-a constructor) is exactly the
    /// asymmetry `SUPPRESS_PROP_MAJOR_ITOA`/`app_arg_type_ok_eager`/
    /// `value_type_ok_eager` exist to route around after the fact — this
    /// redesign avoids creating it in the first place, for the *specific*
    /// subterm (the binder/argument itself) those `eval` calls used to
    /// touch unconditionally.
    ///
    /// Day 10 found this was also the dominant cost on every Acc-shape
    /// export fixture: `eval`'s own reduction-counter hits (`eval` is
    /// called ~55k times inferring `alg-conv-trans-acc-right`'s largest
    /// declaration) came overwhelmingly from this function's own `App`
    /// case eagerly forcing its argument, and its `Lam`/`Pi` cases eagerly
    /// forcing their domain, to build the result — not from either named
    /// rescue helper (confirmed zero invocations with
    /// `KIOTA_TRACE_RESCUE=1`) and not from `infer_type_via_nbe`'s own
    /// `ctx`-re-evaluation loop (confirmed negligible: 221 calls, 594
    /// total `ctx` entries, on the same fixture). Deferring both is this
    /// redesign's actual point: a binder whose type is never looked up,
    /// or an argument whose codomain doesn't depend on it, now costs
    /// nothing instead of a full `eval`.
    ///
    /// Day 12 tried the same treatment for this function's own *return
    /// value* — changing its signature to `R<Rc<nbe::Thunk>>` so `App`'s
    /// own result (the substituted codomain, `body_pi` in an env extended
    /// with the argument) could be `Thunk::deferred` instead of
    /// `self.eval`'d immediately, i.e. eager's `instantiate1`-without-
    /// normalizing, "the Value equivalent of a Closure applied without
    /// forcing." Implemented, sound (`a` itself stayed forced, per Day
    /// 10 — deferring it too reproduced that exact 3x
    /// `080_RBTree.id_spec.accept.ndjson` regression again, even with
    /// `body_pi` also deferred, confirming the two are the same
    /// regression, not two independent ones), full suite green both
    /// flags. Measured *zero* additional `Ir` improvement on all three
    /// Acc-shape fixtures (identical to Day 10's numbers) and a small
    /// (~1.5%) `Ir` regression on `080_RBTree.id_spec.accept.ndjson`
    /// (reproduced across repeated runs, not noise): every caller that
    /// needs to inspect an inferred type's shape — every enclosing `App`
    /// checking `ft` is a `Pi`, every `Lam`/`Pi` checking its domain's
    /// inferred type is a `Sort`, `types_compatible`'s own argument-type
    /// check, and the final `quote` at the declaration boundary — forces
    /// the thunk immediately anyway, via what would have been an
    /// `infer_type_value_forced` helper. For these fixtures' own App
    /// chains, that is *every* level, so the deferred `eval` just moved
    /// from inside this function to the caller's forcing point a moment
    /// later — same total work, plus one `Thunk` allocation's worth of
    /// overhead and no case where the deferral actually paid off. Only a
    /// caller using `infer_only` (skipping the argument-type check
    /// entirely) or one that never inspects the result at all would ever
    /// benefit, and neither pattern shows up enough in these fixtures'
    /// own structure to matter. Reverted (this function still returns
    /// `Rc<nbe::Value>`, `App`'s result is still built by evaluating
    /// `body_pi` under the argument-extended env); Day 11's binder-`Thunk`
    /// work above stays, since it measured as the real win.
    pub(crate) fn infer_type_value(
        &self,
        ctx: &Ctx,
        tys: &[Rc<nbe::Thunk>],
        env: &nbe::VEnv,
        e: &Expr,
    ) -> R<Rc<nbe::Value>> {
        let depth = env.len() as u32;
        match &***e {
            ExprData::BVar(i) => {
                let idx = tys
                    .len()
                    .checked_sub(1 + *i as usize)
                    .ok_or_else(|| TcError::Other("nbe infer: bvar out of range".into()))?;
                tys[idx].force(self)
            }
            ExprData::Sort(l) => Ok(Rc::new(nbe::Value::Sort(level::succ(l.clone())))),
            ExprData::Const(n, us) => {
                let t = self.infer_const(*n, us)?;
                self.eval(&nbe::empty_env(), &t)
            }
            ExprData::Lit(Lit::Nat(_)) => {
                let t = self.nat_type()?;
                self.eval(&nbe::empty_env(), &t)
            }
            ExprData::Lit(Lit::Str(_)) => {
                let t = self.string_type()?;
                self.eval(&nbe::empty_env(), &t)
            }
            ExprData::App(f, a) => {
                let ft = self.infer_type_value(ctx, tys, env, f)?;
                let (dom, env_pi, body_pi) = match &*ft {
                    nbe::Value::Pi(_, dom, pi_env, body) => (dom.clone(), pi_env.clone(), body.clone()),
                    _ => return self.infer_type_value_fallback(ctx, env, e),
                };
                // `dom` is the *function's own* declared parameter type
                // (from `f`'s signature) — bounded by that signature's
                // size, never by `a`'s. Needed unconditionally for the
                // argument-type check below, so forcing it costs the same
                // as eager's own `ensure_pi` needing `dom` as an `Expr`.
                let dom_v = dom.force(self)?;
                // Lean `check` infers every App argument; InferOnly (only
                // ever set for already-checked terms, see `with_infer_only`)
                // skips it, matching the eager App case exactly.
                if !self.infer_only.get() {
                    let at = self.infer_type_value(ctx, tys, env, a)?;
                    if !self.types_compatible(ctx, depth, &at, &dom_v)? && !self.app_arg_type_ok_eager(ctx, f, a)? {
                        if std::env::var_os("KIOTA_DEBUG").is_some() {
                            let at_q = self.quote(depth, &at).unwrap_or_else(|_| a.clone());
                            let dom_q = self.quote(depth, &dom_v).unwrap_or_else(|_| a.clone());
                            let eager_at = self
                                .infer_type_cached(ctx, a)
                                .map(|t| self.pp(&t))
                                .unwrap_or_else(|e| format!("<eager infer failed: {e:?}>"));
                            return reject(format!(
                                "application argument type mismatch (nbe)\n  got:      {}\n  expected: {}\n  eager_at: {}\n  fun:      {}\n  arg:      {}",
                                self.pp(&at_q),
                                self.pp(&dom_q),
                                eager_at,
                                self.pp(f),
                                self.pp(a),
                            ));
                        }
                        return reject("application argument type mismatch (nbe)");
                    }
                }
                // Day 10: tried deferring `a` here too (unconditionally,
                // and gated on whether `body_pi` even references it via
                // `occurs_bvar`) to match `eval`'s own `App` case. Both
                // measured as a large *regression* on
                // `080_RBTree.id_spec.accept.ndjson` — unconditional
                // deferral tripled `eval`'s own call count (47.7k to
                // 157k) and callgrind `Ir` (40.8M to 122.3M) versus eager;
                // gating on `occurs_bvar` alone didn't fix it either
                // (still 157k), meaning whatever interaction causes it
                // isn't simply "the codomain is dependent so it always
                // gets forced anyway" — there's some other, deeper
                // interaction between the extra `Thunk` indirection here
                // and `try_iota_value`'s own re-entry into `apply`/`eval`
                // for this fixture's recursion pattern that this session
                // didn't fully root-cause. Reverted to eager (matching
                // the pre-redesign behavior) rather than ship a
                // regression: `dom` above and the `Lam`/`Pi` cases below
                // still get the `Thunk`-deferred treatment, which
                // measured as a real, non-regressive improvement on every
                // fixture tried.
                let av = self.eval(env, a)?;
                let mut env2 = (*env_pi).clone();
                env2.push(nbe::Thunk::forced(av));
                self.eval(&Rc::new(env2), &body_pi)
            }
            ExprData::Lam(bi, ty, body) => {
                let tt = self.infer_type_value(ctx, tys, env, ty)?;
                if !matches!(&*tt, nbe::Value::Sort(_)) {
                    return self.infer_type_value_fallback(ctx, env, e);
                }
                // Day 10: `ty` (the domain) is deferred, not `eval`'d —
                // see the comment above this function. `vctx_push` stores
                // the thunk directly; `Value::Pi`'s own domain field is
                // already `Rc<Thunk>`, so no forcing happens here either.
                let dom_thunk = nbe::Thunk::deferred(env.clone(), ty.clone());
                let (ctx2, tys2, env2) = Checker::vctx_push(ctx, tys, env, ty, dom_thunk.clone());
                let bt = self.infer_type_value(&ctx2, &tys2, &env2, body)?;
                let bt_q = self.quote(depth + 1, &bt)?;
                Ok(Rc::new(nbe::Value::Pi(*bi, dom_thunk, env.clone(), bt_q)))
            }
            ExprData::Pi(_bi, ty, body) => {
                let tt = self.infer_type_value(ctx, tys, env, ty)?;
                let l1 = match &*tt {
                    nbe::Value::Sort(l) => l.clone(),
                    _ => return self.infer_type_value_fallback(ctx, env, e),
                };
                // Day 10: same deferral as the `Lam` case above. Nothing
                // here needs the domain's *Value*, only the fact that a
                // binder of this type now exists — `bs` (the codomain's
                // own inferred sort) never reads it.
                let dom_thunk = nbe::Thunk::deferred(env.clone(), ty.clone());
                let (ctx2, tys2, env2) = Checker::vctx_push(ctx, tys, env, ty, dom_thunk);
                let bs = self.infer_type_value(&ctx2, &tys2, &env2, body)?;
                let l2 = match &*bs {
                    nbe::Value::Sort(l) => l.clone(),
                    _ => return self.infer_type_value_fallback(ctx, env, e),
                };
                Ok(Rc::new(nbe::Value::Sort(level::imax(l1, l2))))
            }
            ExprData::Let(ty, val, body) => {
                let tt = self.infer_type_value(ctx, tys, env, ty)?;
                if !matches!(&*tt, nbe::Value::Sort(_)) {
                    return self.infer_type_value_fallback(ctx, env, e);
                }
                // `ty` here is the `let`'s own declared annotation, not a
                // subterm of the (potentially huge) value being checked,
                // and `types_compatible` immediately below needs it as a
                // `Value` unconditionally — no laziness opportunity to
                // give up here without skipping the check itself, which
                // would not be sound. Bounded by the annotation's own
                // size, matching eager's own `is_def_eq` cost for `Let`.
                let dom_v = self.eval(env, ty)?;
                let vt = self.infer_type_value(ctx, tys, env, val)?;
                if !self.types_compatible(ctx, depth, &vt, &dom_v)? {
                    return reject("let value type mismatch (nbe)");
                }
                // Zeta first, exactly like `infer_type_uncached`'s own Let
                // case: `ctx` never grows for a `let` (eager substitutes,
                // it doesn't push), so this is the one binder-introducing
                // form that does not call `vctx_push` — matching that
                // keeps `ctx`'s depth in lockstep with the *substituted*
                // term's bvar numbering, with no separate "did ctx grow
                // here" bookkeeping against `tys`/`env` to get wrong.
                let b = expr::instantiate1(body, val);
                self.infer_type_value(ctx, tys, env, &b)
            }
            ExprData::Proj(sname, idx, v) => self.infer_proj_value(ctx, tys, env, *sname, *idx, v),
        }
    }

    /// Value-space counterpart of `infer_proj`: walks the constructor's
    /// declared Pi telescope directly (as `Expr`, since it's a fixed,
    /// closed declaration, not something evaluation ever grows), building
    /// up a `VEnv` of the inductive's own params followed by
    /// `proj(sname, i, v)` for each field before `idx` — so the target
    /// field's domain, `eval`'d against that env, comes out already
    /// substituted, no `instantiate1` needed.
    fn infer_proj_value(
        &self,
        ctx: &Ctx,
        tys: &[Rc<nbe::Thunk>],
        env: &nbe::VEnv,
        sname: u32,
        idx: u32,
        v: &Expr,
    ) -> R<Rc<nbe::Value>> {
        let fallback = |tc: &Self| tc.infer_type_value_fallback_proj(ctx, env, sname, idx, v);
        let vt = self.infer_type_value(ctx, tys, env, v)?;
        let nv = match &*vt {
            nbe::Value::Neutral(nv) => nv,
            _ => return fallback(self),
        };
        let (chead, targs) = Self::unwind_neutral(nv);
        let (ind_name, us) = match chead {
            nbe::Neutral::Const(n, us) => (*n, us.clone()),
            _ => return fallback(self),
        };
        if ind_name != sname {
            return fallback(self);
        }
        let (num_params, ctor_name) = match self.env.get(ind_name) {
            Some(ConstantInfo::InductiveType {
                num_params, ctors, ..
            }) if ctors.len() == 1 => (*num_params, ctors[0]),
            _ => return fallback(self),
        };
        let (ctor_lp, ctor_typ, num_fields) = match self.env.get(ctor_name) {
            Some(ConstantInfo::Constructor {
                level_params,
                typ,
                num_fields,
                ..
            }) => (level_params.clone(), typ.clone(), *num_fields),
            _ => return fallback(self),
        };
        if idx >= num_fields {
            return reject("projection index out of range (nbe)");
        }
        if (targs.len() as u32) < num_params {
            return fallback(self);
        }
        let subst = level::subst_map(&ctor_lp, &us);
        let mut cur = expr::instantiate_level_params(&ctor_typ, &subst);
        let mut fenv: nbe::VEnv = nbe::empty_env();
        for a in targs.iter().take(num_params as usize) {
            let body = match &**cur {
                ExprData::Pi(_, _, body) => body.clone(),
                _ => return fallback(self),
            };
            let pv = a.force(self)?;
            let mut fenv2 = (*fenv).clone();
            fenv2.push(nbe::Thunk::forced(pv));
            fenv = Rc::new(fenv2);
            cur = body;
        }
        let v_value = self.eval(env, v)?;
        for i in 0..idx {
            let body = match &**cur {
                ExprData::Pi(_, _, body) => body.clone(),
                _ => return fallback(self),
            };
            let proj_i = self.eval_proj(sname, i, v_value.clone())?;
            let mut fenv2 = (*fenv).clone();
            fenv2.push(nbe::Thunk::forced(proj_i));
            fenv = Rc::new(fenv2);
            cur = body;
        }
        let dom = match &**cur {
            ExprData::Pi(_, dom, _) => dom.clone(),
            _ => return fallback(self),
        };
        let result = self.eval(&fenv, &dom)?;
        let depth = env.len() as u32;
        let vt_q = self.quote(depth, &vt)?;
        if self.is_prop(ctx, &vt_q)? {
            // Projecting out of a genuinely Prop-valued structure needs
            // the full "does an earlier field's own type get referenced
            // by a later field, and is that earlier field itself data"
            // analysis (see `infer_proj`'s own comment) — not just "is
            // this one field itself Prop", which alone accepts unsound
            // cases like projecting a field that comes after (but does
            // not itself use) a dependent data field
            // (`094_projProp6`/`097_projMaybePropPast`). Rather than
            // reimplement that analysis in Value space for what is an
            // inherently rare, non-hot-path shape, defer to the eager
            // path, which already does it and is kept in sync with any
            // future change to that rule.
            return fallback(self);
        }
        Ok(result)
    }

    fn infer_type_value_fallback_proj(
        &self,
        ctx: &Ctx,
        env: &nbe::VEnv,
        sname: u32,
        idx: u32,
        v: &Expr,
    ) -> R<Rc<nbe::Value>> {
        let t = self.infer_proj(ctx, sname, idx, v)?;
        self.eval(env, &t)
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
        // Day 15: `delta_body_is_small`'s 512-node same-head-delta cap was
        // lifted (it only ever cost completeness, never soundness — see
        // its own doc comment), so it is unconditionally `true` now; this
        // no longer distinguishes small vs. large bodies. What this test
        // actually demonstrates — WHNF's Regular unfolding is unconditional
        // on size, `is_delta` = `has_value`, nothing more — is independent
        // of that cap either way, so it stands on its own below.
        assert!(
            tc.delta_body_is_small(1),
            "abbrev is small for same-head delta"
        );
        assert!(
            tc.delta_body_is_small(2),
            "same-head delta has no size cap post-lift (was: large Regular is not small)"
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
        let tc = Checker::new(&env, &names, None, None);
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
        let tc = Checker::new(&env, &names, None, None);
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
        // `CORE_DEPTH`/`WHNF_DEPTH` are eager-path recursion guards; the NbE
        // spike (`KIOTA_NBE=1`) doesn't share them (`id a` reduces to `a` in
        // O(1) via a closure, no counted recursion to abort), so this
        // eager-internals test has nothing to assert there.
        if crate::nbe::nbe_enabled() {
            return;
        }
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

    // ---------------- NbE spike: eval/quote and is_def_eq_via_nbe vs eager ----------------

    /// `Nat0 : Type`, `Z`/`S` ctors, `Nat0.rec` with the standard two rules —
    /// enough to exercise `try_iota_value`'s "simple" (zero-index,
    /// directly-recursive) path without pulling in the real `Nat` literal
    /// fast path.
    fn insert_mini_nat0(env: &mut crate::env::Environment) {
        use crate::env::{ConstantInfo, RecRule};
        let sort1 = expr::sort(level::succ(level::zero()));
        let nat0 = expr::const_(0, vec![]);
        env.insert(
            0,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: sort1.clone(),
                num_params: 0,
                num_indices: 0,
                all: vec![0],
                ctors: vec![1, 2],
                is_rec: true,
                is_unsafe: false,
            },
        );
        env.insert(
            1,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: nat0.clone(),
                induct: 0,
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            },
        );
        env.insert(
            2,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: expr::pi(expr::BinderInfo::Default, nat0.clone(), nat0.clone()),
                induct: 0,
                cidx: 1,
                num_params: 0,
                num_fields: 1,
                is_unsafe: false,
            },
        );
        env.insert(
            3,
            ConstantInfo::Recursor {
                level_params: vec![],
                typ: sort1,
                all: vec![0],
                num_params: 0,
                num_indices: 0,
                num_motives: 1,
                num_minors: 2,
                rules: vec![
                    RecRule {
                        ctor: 1,
                        nfields: 0,
                        rhs: expr::bvar(0),
                    },
                    RecRule {
                        ctor: 2,
                        nfields: 1,
                        rhs: expr::bvar(0),
                    },
                ],
                k: false,
                is_unsafe: false,
            },
        );
        env.rec_of.insert(0, 3);
    }

    fn nat0_lit(n: u32) -> Expr {
        let z = expr::const_(1, vec![]);
        let s = expr::const_(2, vec![]);
        let mut cur = z;
        for _ in 0..n {
            cur = expr::app(s.clone(), cur);
        }
        cur
    }

    /// `Nat0.rec motive 1 (fun _ ih => S ih) 2` (i.e. `add 2 1`) must NbE-
    /// evaluate, quote, and `is_def_eq_via_nbe` all agree with eager on `3`,
    /// and must not agree on `2` — the closure-based iota path in
    /// `try_iota_value`/`build_rec_call_value` has to reduce a real
    /// `brecOn`-shaped recursive call (one rec-call per level, via a
    /// `Thunk::RecCall`, not a re-quoted term) to the right answer.
    #[test]
    fn nbe_nat0_rec_add_matches_eager() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_nat0(&mut env);
        let names = test_names(&["Nat0", "Nat0.Z", "Nat0.S", "Nat0.rec"]);
        let tc = Checker::new(&env, &names, None, None);

        let nat0 = expr::const_(0, vec![]);
        let s = expr::const_(2, vec![]);
        let rec_ = expr::const_(3, vec![]);
        let motive = expr::lam(expr::BinderInfo::Default, nat0.clone(), nat0.clone());
        let base = nat0_lit(1); // add's `m`
        let step = expr::lam(
            expr::BinderInfo::Default,
            nat0.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                nat0,
                expr::app(s, expr::bvar(0)),
            ),
        );
        let two = nat0_lit(2);
        let rec_app = expr::apps(rec_, &[motive, base, step, two.clone()]);
        let three = nat0_lit(3);

        let ctx = Ctx::new();
        assert!(
            tc.is_def_eq(&ctx, &rec_app, &three).unwrap(),
            "eager: add 2 1 must convert to 3"
        );
        assert!(
            tc.is_def_eq_via_nbe(&ctx, &rec_app, &three).unwrap(),
            "nbe: add 2 1 must convert to 3"
        );
        assert!(
            !tc.is_def_eq(&ctx, &rec_app, &two).unwrap(),
            "eager: add 2 1 must not convert to 2"
        );
        assert!(
            !tc.is_def_eq_via_nbe(&ctx, &rec_app, &two).unwrap(),
            "nbe: add 2 1 must not convert to 2"
        );

        // eval/quote round-trip: the quoted normal form must itself be
        // eager-defeq to `3` (and NOT to `2`).
        let v = tc.eval(&crate::nbe::generic_env(0), &rec_app).unwrap();
        let q = tc.quote(0, &v).unwrap();
        assert!(
            tc.is_def_eq(&ctx, &q, &three).unwrap(),
            "quoted NbE normal form must eager-convert to 3, got {}",
            tc.pp(&q)
        );
        assert!(!tc.is_def_eq(&ctx, &q, &two).unwrap());
    }

    /// Closed beta/eta-free lambda application: `(fun _:A => a) star` vs
    /// `a`. Smallest possible eval/quote + `is_def_eq_via_nbe` sanity check,
    /// independent of any inductive/iota machinery.
    #[test]
    fn nbe_beta_matches_eager_on_axioms() {
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
        env.insert(
            2,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: expr::const_(0, vec![]),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "a", "star"]);
        let tc = Checker::new(&env, &names, None, None);
        let a_ty = expr::const_(0, vec![]);
        let a = expr::const_(1, vec![]);
        let star = expr::const_(2, vec![]);
        let redex = expr::app(
            expr::lam(expr::BinderInfo::Default, a_ty, a.clone()),
            star,
        );
        let ctx = Ctx::new();
        assert!(tc.is_def_eq(&ctx, &redex, &a).unwrap());
        assert!(tc.is_def_eq_via_nbe(&ctx, &redex, &a).unwrap());
        assert!(!tc.is_def_eq(&ctx, &redex, &expr::const_(2, vec![])).unwrap());
        assert!(!tc
            .is_def_eq_via_nbe(&ctx, &redex, &expr::const_(2, vec![]))
            .unwrap());

        let v = tc.eval(&crate::nbe::generic_env(0), &redex).unwrap();
        let q = tc.quote(0, &v).unwrap();
        assert!(Rc::ptr_eq(&q, &a), "quoted beta-redex must be `a` itself, got {}", tc.pp(&q));
    }

    /// The `KIOTA_NBE=1` dispatch in `is_def_eq` must be a pure accelerator:
    /// running the whole exports suite through it must not change any
    /// accept/reject/decline verdict. `run_all_flag_combinations.sh`/CI sets
    /// the env var; here we call `is_def_eq_via_nbe` directly so the test is
    /// deterministic regardless of how the test binary itself was launched.
    #[test]
    fn nbe_never_confirms_true_when_eager_says_false() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_nat0(&mut env);
        let names = test_names(&["Nat0", "Nat0.Z", "Nat0.S", "Nat0.rec"]);
        let tc = Checker::new(&env, &names, None, None);
        let ctx = Ctx::new();
        // Two unrelated numerals: NbE must not spuriously confirm equality.
        for i in 0..5u32 {
            for j in 0..5u32 {
                let a = nat0_lit(i);
                let b = nat0_lit(j);
                let eager = tc.is_def_eq(&ctx, &a, &b).unwrap();
                let nbe = tc.is_def_eq_via_nbe(&ctx, &a, &b).unwrap();
                assert_eq!(eager, i == j);
                assert_eq!(nbe, eager, "nbe/eager disagree on Nat0 {i} vs {j}");
            }
        }
    }

    // ---------------- Eager recursor-application memo (Day 2 build order) ----------------

    /// Same shape as `insert_mini_nat0`, but wired as the checker's `Nat`
    /// (`nat_ref = Some(0)`) so a real `Lit::Nat` major exercises
    /// `try_iota`'s literal-peel branch and `iota_lit_memo`, not the
    /// constructor-tower path `insert_mini_nat0`'s own tests use.
    fn insert_mini_natlit(env: &mut crate::env::Environment) {
        insert_mini_nat0(env);
    }

    /// `add(n, 1) := Nat.rec 1 (fun _ ih => S ih) (lit n)`. Compared against
    /// a `Nat0.Z`/`Nat0.S` ctor tower (`nat0_lit`), not a raw literal on the
    /// RHS: `numeral_value`'s congruence shortcut inspects a term's shape
    /// as-is rather than forcing it, so a stuck `Nat.rec` spine only gets
    /// peeled level by level through `app_spines_congruent`'s recursive
    /// `is_def_eq` on the `S`'s argument — which is exactly the recursion
    /// this memo targets.
    fn add_one_rec_app(motive: &Expr, step: &Expr, n: u32) -> Expr {
        let rec_ = expr::const_(3, vec![]);
        let base = expr::lit_nat(num_bigint::BigUint::from(1u32));
        expr::apps(
            rec_,
            &[
                motive.clone(),
                base,
                step.clone(),
                expr::lit_nat(num_bigint::BigUint::from(n)),
            ],
        )
    }

    /// The operator's build order: (1) instrument to confirm the same
    /// `(recursor, motive, minors)` triple recurs at overlapping literals,
    /// (2) memoize it. This reproduces exactly that overlap: a first
    /// `add(10, 1)` peels literals 10..=0 into `iota_lit_memo`; a second,
    /// independent `add(7, 1)` — same motive/minor *pointers*, an entirely
    /// separate top-level term, not reachable via the ordinary
    /// `(ctx, ptr)` whnf cache — revisits literals 7..=0, all of which
    /// should now be memo hits. `iota_lit_memo_miss_count` (real
    /// `iota_from_first_principles` derivations) makes that observable
    /// instead of only inferring it from wall-clock time.
    #[test]
    fn eager_iota_lit_memo_reuses_overlapping_countdown() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_natlit(&mut env);
        let names = test_names(&["Nat0", "Nat0.Z", "Nat0.S", "Nat0.rec"]);
        let tc = Checker::new(&env, &names, Some(0), None);
        let ctx = Ctx::new();

        let nat0 = expr::const_(0, vec![]);
        let motive = expr::lam(expr::BinderInfo::Default, nat0.clone(), nat0.clone());
        let s = expr::const_(2, vec![]);
        let step = expr::lam(
            expr::BinderInfo::Default,
            nat0.clone(),
            expr::lam(expr::BinderInfo::Default, nat0, expr::app(s, expr::bvar(0))),
        );

        let ten = add_one_rec_app(&motive, &step, 10);
        let eleven = nat0_lit(11);
        assert!(tc.is_def_eq(&ctx, &ten, &eleven).unwrap(), "add 10 1 must convert to 11");
        let misses_after_first = tc.iota_lit_memo_miss_count();
        assert!(
            misses_after_first >= 11,
            "first countdown (11 levels, 10..=0) must derive each peel at least once, got {misses_after_first}"
        );

        // Independent term (fresh `expr::apps` spine, not reachable from
        // `ten` via `(ctx, ptr)`), overlapping literals 7..=0.
        let seven = add_one_rec_app(&motive, &step, 7);
        let eight = nat0_lit(8);
        assert!(tc.is_def_eq(&ctx, &seven, &eight).unwrap(), "add 7 1 must convert to 8");
        let misses_after_second = tc.iota_lit_memo_miss_count();
        assert_eq!(
            misses_after_second, misses_after_first,
            "every literal in the second (overlapping) countdown must hit iota_lit_memo, not re-derive"
        );
    }

    /// Same overlap with the memo forced off on this `Checker` (test-only
    /// override, not the process-wide `KIOTA_NO_IOTA_MEMO` env var — that
    /// would race with other tests' `try_iota` calls under `cargo test`'s
    /// parallel test threads): correctness must not depend on the memo.
    ///
    /// This also empirically confirms (rather than assumes) something the
    /// build order didn't anticipate: with the memo off, the *first*
    /// countdown still derives every peel (>= 11), but the *second*,
    /// overlapping one derives **zero** more. That is not this memo at
    /// work (it is disabled) — it is `whnf_cache`/`defeq_cache`, keyed on
    /// `(ctx, ptr)`, already sharing the intermediate `Nat0.rec motive
    /// base step (lit k)` terms for `k` in the overlap, because they are
    /// pointer-identical (interned) across both countdowns. So on *this*
    /// idealized reproduction — shared `motive`/`minors` pointers, an
    /// interned literal — `iota_lit_memo` is redundant with caching kiota
    /// already had; it can only add value where a (ctx, ptr) hit is not
    /// available (e.g. across separate `Checker`s, or if two occurrences
    /// of "the same" recursor call are ever *not* pointer-identical).
    #[test]
    fn eager_iota_lit_memo_disable_still_correct() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_natlit(&mut env);
        let names = test_names(&["Nat0", "Nat0.Z", "Nat0.S", "Nat0.rec"]);
        let tc = Checker::new(&env, &names, Some(0), None);
        tc.set_iota_memo_enabled_for_test(false);
        let ctx = Ctx::new();
        let nat0 = expr::const_(0, vec![]);
        let motive = expr::lam(expr::BinderInfo::Default, nat0.clone(), nat0.clone());
        let s = expr::const_(2, vec![]);
        let step = expr::lam(
            expr::BinderInfo::Default,
            nat0.clone(),
            expr::lam(expr::BinderInfo::Default, nat0, expr::app(s, expr::bvar(0))),
        );
        let ten = add_one_rec_app(&motive, &step, 10);
        let eleven = nat0_lit(11);
        assert!(tc.is_def_eq(&ctx, &ten, &eleven).unwrap());
        let misses_after_first = tc.iota_lit_memo_miss_count();
        assert!(
            misses_after_first >= 11,
            "memo disabled: first countdown must still fully re-derive (>= 11 peels), got {misses_after_first}"
        );
        let seven = add_one_rec_app(&motive, &step, 7);
        let eight = nat0_lit(8);
        assert!(tc.is_def_eq(&ctx, &seven, &eight).unwrap());
        let misses_after_second = tc.iota_lit_memo_miss_count();
        assert_eq!(
            misses_after_second, misses_after_first,
            "with the memo off, the overlap is still free — that's whnf_cache/defeq_cache \
             (ctx, ptr) sharing the interned intermediate terms, not iota_lit_memo"
        );
    }

    // ---------------- NbE spike, Day 4: infer_type_value vs eager ----------------

    /// `A : Type`, `a : A`, `id := fun (_:A) => A` (so `App`'s codomain
    /// exercises the beta step), `f := fun (x:A) => let (_:A) := a; x`.
    /// Runs `infer_type_value` on `f`'s *body* — a `Lam` nested inside a
    /// `Let` — and checks the quoted result agrees with eager `infer_type`
    /// on the same term, at the same context depth.
    #[test]
    fn infer_type_value_matches_eager_on_lam_pi_app_let() {
        use crate::env::{ConstantInfo, Environment};
        let mut env = Environment::default();
        let sort1 = expr::sort(level::succ(level::zero()));
        env.insert(
            0,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: sort1,
                is_unsafe: false,
            },
        );
        let a_ty = expr::const_(0, vec![]);
        env.insert(
            1,
            ConstantInfo::Axiom {
                level_params: vec![],
                typ: a_ty.clone(),
                is_unsafe: false,
            },
        );
        let names = test_names(&["A", "a"]);
        let tc = Checker::new(&env, &names, None, None);
        let a_val = expr::const_(1, vec![]);

        // `fun (x:A) => let (_:A) := a; x` : `A -> A`.
        let inner_let = expr::let_(a_ty.clone(), a_val.clone(), expr::bvar(1));
        let f = expr::lam(expr::BinderInfo::Default, a_ty.clone(), inner_let);

        let (tys, venv) = Checker::vctx_new();
        let ctx = Ctx::new();
        let ft_v = tc.infer_type_value(&ctx, &tys, &venv, &f).unwrap();
        let ft_q = tc.quote(0, &ft_v).unwrap();
        let ft_eager = tc.infer_type(&ctx, &f).unwrap();
        assert!(
            tc.is_def_eq(&ctx, &ft_q, &ft_eager).unwrap(),
            "infer_type_value(f) = {} must eager-convert to infer_type(f) = {}",
            tc.pp(&ft_q),
            tc.pp(&ft_eager)
        );
        // `f`'s type must actually be `A -> A` (Pi, not stuck).
        assert!(matches!(&*ft_v, nbe::Value::Pi(..)));

        // Applying `f` to `a` must type-check (App's argument-type path)
        // and infer `A`.
        let app = expr::app(f, a_val);
        let at_v = tc.infer_type_value(&ctx, &tys, &venv, &app).unwrap();
        let at_q = tc.quote(0, &at_v).unwrap();
        assert!(
            tc.is_def_eq(&ctx, &at_q, &a_ty).unwrap(),
            "infer_type_value(f a) must be A, got {}",
            tc.pp(&at_q)
        );

        // Ill-typed application (wrong argument type) must reject, not
        // silently accept: `f` applied to `A` itself (a `Sort`, not an
        // `A`) is not well-typed.
        let bad_app = expr::app(
            expr::lam(expr::BinderInfo::Default, a_ty.clone(), expr::bvar(0)),
            a_ty,
        );
        assert!(tc.infer_type_value(&ctx, &tys, &venv, &bad_app).is_err());
    }

    /// `PSigma.rec α β motive minor (mk α β x y)`'s projection form:
    /// `infer_type_value` of `proj 0 0 #0` (first field of a bound
    /// `PSigma A B`) must agree with eager `infer_proj`.
    #[test]
    fn infer_type_value_matches_eager_on_proj() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_psigma(&mut env);
        let names = test_names(&["PSigma", "PSigma.mk", "PSigma.rec", "A", "B"]);
        let tc = Checker::new(&env, &names, None, None);
        let a = expr::const_(3, vec![]);
        let b = expr::const_(4, vec![]);
        let psigma_ab = expr::apps(expr::const_(0, vec![]), &[a.clone(), b]);

        let (tys0, venv0) = Checker::vctx_new();
        let ctx0 = Ctx::new();
        let psigma_ty_v = tc.infer_type_value(&ctx0, &tys0, &venv0, &psigma_ab).unwrap();
        // `Sort 1`, so the binder we push below matches the eager `ensure_sort`
        // path that would've been used to introduce this same bvar.
        assert!(matches!(&*psigma_ty_v, nbe::Value::Sort(_)));
        let psigma_ty_val = tc.eval(&venv0, &psigma_ab).unwrap();
        let (ctx, tys, venv) = Checker::vctx_push(
            &ctx0,
            &tys0,
            &venv0,
            &psigma_ab,
            nbe::Thunk::forced(psigma_ty_val),
        );

        let proj0 = expr::proj(0, 0, expr::bvar(0));
        let t_v = tc.infer_type_value(&ctx, &tys, &venv, &proj0).unwrap();
        let t_q = tc.quote(1, &t_v).unwrap();

        let t_eager = tc.infer_proj(&ctx, 0, 0, &expr::bvar(0)).unwrap();
        assert!(
            tc.is_def_eq(&ctx, &t_q, &t_eager).unwrap(),
            "infer_type_value(proj 0 0 #0) = {} must eager-convert to infer_proj = {}",
            tc.pp(&t_q),
            tc.pp(&t_eager)
        );
        assert!(Rc::ptr_eq(&t_q, &a), "first field of PSigma A B must infer to A, got {}", tc.pp(&t_q));
    }

    // ---------------- NbE spike, Day 7: indexed + higher-order iota ----------------
    //
    // Day 6 found the actual gap behind the two failing accept fixtures
    // (`alg-conv-trans-acc-left`, `subject-reduction-redex`): eager reduces
    // `Acc.rec motive minor x (Acc.intro x g)` via ordinary iota (a
    // literal-constructor major), and the Value-native path couldn't —
    // `Acc` has a nonzero index (`num_indices`), which `try_iota_value`
    // bailed on immediately, and separately `Acc.intro`'s one field has
    // type `∀ y, r y x → Acc r y` — a `Pi`, not a bare recursive
    // occurrence, needing a binder-introducing rec-call `try_iota_value`
    // didn't build.
    //
    // Day 7 implements both. `try_iota_value` no longer special-cases
    // `num_indices` at all — indices are just extra major-position
    // arguments, skipped exactly like eager `try_iota` skips them. Once a
    // literal-constructor (or `Nat`-literal, or theorem-unfolds-to-one,
    // via `recursor_unfolds_thm_major`/`whnf_major`) major is found, the
    // "apply minor to fields, interleave one rec-call per recursive field"
    // step is not reimplemented in Value space at all: it calls eager's
    // own `iota_from_first_principles`/`mk_rec_call` directly on quoted
    // (bounded, non-accumulating) params/motives/minors/fields, guaranteeing
    // it matches eager's rule by construction — including indices threaded
    // through a field's own occurrence type, and higher-order fields,
    // which come back as a genuine `Value::Lam` (a real closure, not a
    // quoted-and-reevaluated stand-in) ready to be applied to fresh
    // arguments exactly like any other value.
    fn insert_mini_acc(env: &mut crate::env::Environment) {
        use crate::env::{ConstantInfo, RecRule};
        let sort0 = expr::sort(level::zero());
        let sort1 = expr::sort(level::succ(level::zero()));
        let nat = expr::const_(0, vec![]);
        // `MyAcc : Nat -> Prop` (one index, no params) — mirrors `Acc`'s
        // shape (`Acc {α} (r : α → α → Prop) (x : α) : Prop`) collapsed to
        // a fixed carrier/relation for the test.
        let myacc_ty = expr::pi(expr::BinderInfo::Default, nat.clone(), sort0.clone());
        env.insert(
            1,
            ConstantInfo::InductiveType {
                level_params: vec![],
                typ: myacc_ty.clone(),
                num_params: 0,
                num_indices: 1,
                all: vec![1],
                ctors: vec![2],
                is_rec: true,
                is_unsafe: false,
            },
        );
        // `MyAcc.intro : (x : Nat) -> (∀ y, MyAcc y) -> MyAcc x` — the one
        // field is a `Pi` returning the recursive occurrence, exactly
        // `Acc.intro`'s higher-order shape (`∀ y, r y x → Acc r y`), just
        // without the relation-membership hypothesis (irrelevant to the
        // "is this field a bare recursive occurrence" question).
        let field_ty = expr::pi(expr::BinderInfo::Default, nat.clone(), expr::app(expr::const_(1, vec![]), expr::bvar(0)));
        let intro_ty = expr::pi(
            expr::BinderInfo::Default,
            nat.clone(),
            expr::pi(
                expr::BinderInfo::Default,
                field_ty,
                expr::app(expr::const_(1, vec![]), expr::bvar(1)),
            ),
        );
        env.insert(
            2,
            ConstantInfo::Constructor {
                level_params: vec![],
                typ: intro_ty,
                induct: 1,
                cidx: 0,
                num_params: 0,
                num_fields: 2,
                is_unsafe: false,
            },
        );
        // `MyAcc.rec : (motive : Nat -> MyAcc #0 -> Sort 1) -> (minor) -> (x : Nat) -> (h : MyAcc x) -> motive x h`.
        // The exact motive/minor types don't matter for `try_iota_value`
        // (it never inspects them beyond position), only the telescope
        // shape (`num_params=0, num_motives=1, num_minors=1, num_indices=1`).
        env.insert(
            3,
            ConstantInfo::Recursor {
                level_params: vec![],
                typ: sort1,
                all: vec![1],
                num_params: 0,
                num_indices: 1,
                num_motives: 1,
                num_minors: 1,
                rules: vec![RecRule {
                    ctor: 2,
                    nfields: 2,
                    rhs: expr::bvar(0),
                }],
                k: false,
                is_unsafe: false,
            },
        );
        env.rec_of.insert(1, 3);
    }

    /// Shared plumbing for the Day 7 `MyAcc.rec` tests: `motive` and
    /// `minor` (arity 3: the index field, the `g` field, and the "ih"
    /// rec-call — matching `iota_from_first_principles`'s field-then-rec
    /// ordering for `MyAcc.intro`'s two fields, one of which is
    /// recursive).
    fn mini_acc_motive_and_minor() -> (Expr, Expr) {
        let nat = expr::const_(0, vec![]);
        let motive = expr::lam(
            expr::BinderInfo::Default,
            nat.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                expr::app(expr::const_(1, vec![]), expr::bvar(0)),
                nat.clone(),
            ),
        );
        // `minor := fun (x:Nat) (g : Nat -> MyAcc) (ih : Nat -> Nat) => x`
        // (`x` referenced as `#2`, three binders deep): discards `g` and
        // `ih` entirely and returns the index field it was actually
        // applied to. A minor that ignores `ih` must never force it —
        // exactly the laziness `eval`'s `App` case already gives any
        // argument thunk, now exercised through the bridge in
        // `try_iota_value` instead of the old dedicated `Thunk::RecCall`.
        let minor = expr::lam(
            expr::BinderInfo::Default,
            nat.clone(),
            expr::lam(
                expr::BinderInfo::Default,
                expr::pi(
                    expr::BinderInfo::Default,
                    nat.clone(),
                    expr::app(expr::const_(1, vec![]), expr::bvar(0)),
                ),
                expr::lam(
                    expr::BinderInfo::Default,
                    expr::pi(expr::BinderInfo::Default, nat.clone(), nat.clone()),
                    expr::bvar(2),
                ),
            ),
        );
        (motive, minor)
    }

    /// `MyAcc.rec motive minor x (MyAcc.intro x g)` — a literal-constructor
    /// major over an *indexed* recursor whose recursive field is *higher-
    /// order* (`Pi`-shaped), exactly `Acc.rec`/`Acc.intro`'s shape — must
    /// now reduce, matching eager `try_iota`'s rule exactly (via the
    /// `iota_from_first_principles`/`mk_rec_call` bridge), not decline.
    /// `minor` discards both the field `g` and the rec-call `ih`, so the
    /// correct answer is simply `x` — and since nothing ever forces `g`,
    /// `g`'s own body doesn't need to be well-typed for this test (it
    /// never gets evaluated).
    #[test]
    fn try_iota_value_reduces_indexed_higher_order_ctor_major() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_acc(&mut env);
        let names = test_names(&["Nat0", "MyAcc", "MyAcc.intro", "MyAcc.rec"]);
        let tc = Checker::new(&env, &names, None, None);

        let nat = expr::const_(0, vec![]);
        let x = expr::lit_nat(num_bigint::BigUint::from(7u32));
        let (motive, minor) = mini_acc_motive_and_minor();
        // `g`'s body is never forced by `minor` (which discards it), so a
        // syntactically-closed placeholder is enough.
        let g = expr::lam(expr::BinderInfo::Default, nat, x.clone());
        let intro = expr::apps(expr::const_(2, vec![]), &[x.clone(), g]);
        let rec_app = expr::apps(expr::const_(3, vec![]), &[motive, minor, x.clone(), intro]);

        let v = tc.eval(&crate::nbe::generic_env(0), &rec_app).unwrap();
        match &*v {
            nbe::Value::Lit(Lit::Nat(n)) => {
                assert_eq!(*n, num_bigint::BigUint::from(7u32));
            }
            other => panic!(
                "MyAcc.rec on a literal MyAcc.intro major must reduce to the index (7), got {}",
                tc.pp(&tc.quote(0, other).unwrap())
            ),
        }
    }

    /// The same recursor and minor, but the major is a bound variable —
    /// not a constructor application at all. Must still correctly decline
    /// (stay a stuck `Neutral`), the same as before Day 7: the indexed/
    /// higher-order rule only ever fires once a real constructor (or
    /// theorem-unfolds-to-one) major is found.
    #[test]
    fn try_iota_value_still_declines_when_major_is_not_a_ctor() {
        use crate::env::Environment;
        let mut env = Environment::default();
        insert_mini_acc(&mut env);
        let names = test_names(&["Nat0", "MyAcc", "MyAcc.intro", "MyAcc.rec"]);
        let tc = Checker::new(&env, &names, None, None);

        let x = expr::lit_nat(num_bigint::BigUint::from(7u32));
        let (motive, minor) = mini_acc_motive_and_minor();
        let major_var = expr::bvar(0);
        let rec_app = expr::apps(expr::const_(3, vec![]), &[motive, minor, x, major_var]);

        let env1 = crate::nbe::generic_env(1);
        let v = tc.eval(&env1, &rec_app).unwrap();
        assert!(
            matches!(&*v, nbe::Value::Neutral(_)),
            "a non-constructor major must stay neutral (declined, not reduced), got {}",
            tc.pp(&tc.quote(1, &v).unwrap())
        );
    }

    // ---------------- NbE spike, Day 7 continued: the eager-rescue wiring bug ----------------
    //
    // The two Acc-shape export fixtures still rejected with `infer_type`
    // wired even after `try_iota_value` grew the indexed/higher-order
    // rule: eager's own comparison never re-derives an `Acc.rec`-headed
    // type at all — it succeeds by comparing an *unreduced* wrapper
    // application (`f 1 h` vs `f 1 (Acc.intro …)`) via proof irrelevance
    // on the wrapper's own Prop-typed parameter, never even unfolding the
    // wrapper. `infer_type_value`'s `App` case, by contrast, always calls
    // `eval` (which always fully reduces, unfolding the wrapper and then
    // iota-reducing its `Acc.rec`), so the value-native path can see an
    // asymmetric "peel" (one side's major stayed a bound variable, the
    // other's — theorem-wrapped or not — was already a literal
    // constructor) that never arises for eager because eager never
    // reduces that far. `app_arg_type_ok_eager`/`value_type_ok_eager`
    // exist to re-run that exact eager comparison as a rescue, but the
    // rescue itself had two more bugs before it actually stayed eager
    // end to end (both now covered by `alg_conv_trans_acc_left_accepts`/
    // `subject_reduction_redex_accepts` in `tests/exports.rs`, which
    // reject without either fix and accept with both — that pair of real,
    // Lean-exported fixtures is the regression test for this section; a
    // synthetic in-crate repro needs a fully Pi-typed stand-in recursor,
    // which the existing `insert_mini_acc` test fixture deliberately
    // isn't, to actually exercise the recursive dispatch path below):
    //
    // 1. `pub fn is_def_eq`'s `FORCE_EAGER_DEFEQ` gate stayed eager for
    //    its own top-level call, but `is_def_eq_core_go`'s own recursion
    //    (Pi/Lam bodies) calls the *dispatching* `is_def_eq`, not
    //    `is_def_eq_inner` — so a rescue's comparison re-entered NbE (and
    //    could re-hit the same over-reduction) as soon as it recursed
    //    past the outermost node. Fixed by making `FORCE_EAGER_DEFEQ`
    //    thread through `pub fn is_def_eq`'s own dispatch, not just the
    //    rescue's initial call.
    // 2. `pub fn infer_type`'s dispatch checked only `nbe::nbe_enabled()`,
    //    never `FORCE_EAGER_DEFEQ` at all — so `infer_type_uncached`'s
    //    own recursive calls (App's `f`/`a`, Lam's body, …), which go
    //    through the *dispatching* `infer_type`, kept re-entering
    //    `infer_type_via_nbe` for every sub-expression even while a
    //    rescue's outermost call used `infer_type_cached` directly. This
    //    was the one that actually mattered for both fixtures.
    //
    // Both `defeq_cache`/`infer_cache`/`whnf_cache`/`whnf_core_cache` also
    // skip reading and writing while `FORCE_EAGER_DEFEQ` is set, so a
    // rescue can't read a stale entry a non-forced call populated (or
    // vice versa) for the same `(ctx, expr)` key.
}
