use crate::level::Level;
use rustc_hash::{FxHashMap, FxHasher};
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    Nat(num_bigint::BigUint),
    Str(Rc<String>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    BVar(u32),
    Sort(Level),
    Const(u32, Rc<Vec<Level>>), // name index, universe args
    App(Expr, Expr),
    Lam(BinderInfo, Expr, Expr), // type, body
    Pi(BinderInfo, Expr, Expr),  // type, body
    Let(Expr, Expr, Expr),       // type, value, body
    Proj(u32, u32, Expr),        // struct name index, field index, struct value
    Lit(Lit),
}

pub type Expr = Rc<ExprData>;

fn ptr(e: &Expr) -> usize {
    Rc::as_ptr(e) as usize
}

fn hash_node(d: &ExprData) -> u64 {
    let mut h = FxHasher::default();
    match d {
        ExprData::BVar(i) => {
            0u8.hash(&mut h);
            i.hash(&mut h);
        }
        ExprData::Sort(l) => {
            1u8.hash(&mut h);
            l.hash(&mut h);
        }
        ExprData::Const(n, us) => {
            2u8.hash(&mut h);
            n.hash(&mut h);
            us.hash(&mut h);
        }
        ExprData::App(f, a) => {
            3u8.hash(&mut h);
            ptr(f).hash(&mut h);
            ptr(a).hash(&mut h);
        }
        ExprData::Lam(bi, ty, body) => {
            4u8.hash(&mut h);
            (*bi as u8).hash(&mut h);
            ptr(ty).hash(&mut h);
            ptr(body).hash(&mut h);
        }
        ExprData::Pi(bi, ty, body) => {
            5u8.hash(&mut h);
            (*bi as u8).hash(&mut h);
            ptr(ty).hash(&mut h);
            ptr(body).hash(&mut h);
        }
        ExprData::Let(ty, val, body) => {
            6u8.hash(&mut h);
            ptr(ty).hash(&mut h);
            ptr(val).hash(&mut h);
            ptr(body).hash(&mut h);
        }
        ExprData::Proj(s, i, v) => {
            7u8.hash(&mut h);
            s.hash(&mut h);
            i.hash(&mut h);
            ptr(v).hash(&mut h);
        }
        ExprData::Lit(Lit::Nat(n)) => {
            8u8.hash(&mut h);
            n.hash(&mut h);
        }
        ExprData::Lit(Lit::Str(s)) => {
            9u8.hash(&mut h);
            s.hash(&mut h);
        }
    }
    h.finish()
}

fn node_eq(a: &ExprData, b: &ExprData) -> bool {
    match (a, b) {
        (ExprData::BVar(i), ExprData::BVar(j)) => i == j,
        (ExprData::Sort(x), ExprData::Sort(y)) => x == y,
        (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) => n1 == n2 && u1 == u2,
        (ExprData::App(f1, a1), ExprData::App(f2, a2)) => Rc::ptr_eq(f1, f2) && Rc::ptr_eq(a1, a2),
        (ExprData::Lam(b1, t1, x1), ExprData::Lam(b2, t2, x2)) => {
            b1 == b2 && Rc::ptr_eq(t1, t2) && Rc::ptr_eq(x1, x2)
        }
        (ExprData::Pi(b1, t1, x1), ExprData::Pi(b2, t2, x2)) => {
            b1 == b2 && Rc::ptr_eq(t1, t2) && Rc::ptr_eq(x1, x2)
        }
        (ExprData::Let(t1, v1, b1), ExprData::Let(t2, v2, b2)) => {
            Rc::ptr_eq(t1, t2) && Rc::ptr_eq(v1, v2) && Rc::ptr_eq(b1, b2)
        }
        (ExprData::Proj(s1, i1, v1), ExprData::Proj(s2, i2, v2)) => {
            s1 == s2 && i1 == i2 && Rc::ptr_eq(v1, v2)
        }
        (ExprData::Lit(x), ExprData::Lit(y)) => x == y,
        _ => false,
    }
}

#[derive(Default)]
struct Interner {
    buckets: FxHashMap<u64, Vec<Expr>>,
}

impl Interner {
    fn intern(&mut self, d: ExprData) -> Expr {
        let h = hash_node(&d);
        if let Some(bucket) = self.buckets.get(&h) {
            for e in bucket {
                if node_eq(&d, e) {
                    return e.clone();
                }
            }
        }
        let e = Rc::new(d);
        self.buckets.entry(h).or_default().push(e.clone());
        e
    }
}

thread_local! {
    static INTERN: RefCell<Interner> = RefCell::new(Interner::default());
}

pub fn intern(d: ExprData) -> Expr {
    INTERN.with(|t| t.borrow_mut().intern(d))
}

pub fn bvar(i: u32) -> Expr {
    intern(ExprData::BVar(i))
}
pub fn sort(l: Level) -> Expr {
    intern(ExprData::Sort(l))
}
pub fn const_(n: u32, us: Vec<Level>) -> Expr {
    intern(ExprData::Const(n, Rc::new(us)))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    intern(ExprData::App(f, a))
}
pub fn lam(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    intern(ExprData::Lam(bi, ty, body))
}
pub fn pi(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    intern(ExprData::Pi(bi, ty, body))
}
pub fn let_(ty: Expr, val: Expr, body: Expr) -> Expr {
    intern(ExprData::Let(ty, val, body))
}
pub fn proj(s: u32, i: u32, e: Expr) -> Expr {
    intern(ExprData::Proj(s, i, e))
}
pub fn lit_nat(n: num_bigint::BigUint) -> Expr {
    intern(ExprData::Lit(Lit::Nat(n)))
}
pub fn lit_str(s: impl Into<String>) -> Expr {
    intern(ExprData::Lit(Lit::Str(Rc::new(s.into()))))
}

thread_local! {
    static CLOSED: RefCell<FxHashMap<usize, bool>> = RefCell::new(FxHashMap::default());
}

/// True when `e` has no loose bvars. Memoized on interned pointers.
pub fn is_closed(e: &Expr) -> bool {
    closed_at(e, 0)
}

fn closed_at(e: &Expr, depth: u32) -> bool {
    if depth == 0 {
        let k = ptr(e);
        if let Some(c) = CLOSED.with(|m| m.borrow().get(&k).copied()) {
            return c;
        }
        let c = closed_at_go(e, 0);
        CLOSED.with(|m| {
            m.borrow_mut().insert(k, c);
        });
        return c;
    }
    closed_at_go(e, depth)
}

fn closed_at_go(e: &Expr, depth: u32) -> bool {
    match &**e {
        ExprData::BVar(i) => *i < depth,
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => true,
        ExprData::App(f, a) => closed_at(f, depth) && closed_at(a, depth),
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            closed_at(ty, depth) && closed_at(body, depth + 1)
        }
        ExprData::Let(ty, val, body) => {
            closed_at(ty, depth) && closed_at(val, depth) && closed_at(body, depth + 1)
        }
        ExprData::Proj(_, _, v) => closed_at(v, depth),
    }
}

pub fn apps(f: Expr, args: &[Expr]) -> Expr {
    let mut r = f;
    for a in args {
        r = app(r, a.clone());
    }
    r
}

/// Shift free (>= cutoff) de Bruijn indices by `by` (can be used with negative
/// effectively only in controlled contexts; we only ever shift up here).
pub fn shift(e: &Expr, by: i32, cutoff: u32) -> Expr {
    if by == 0 {
        return e.clone();
    }
    match &**e {
        ExprData::BVar(i) => {
            if *i >= cutoff {
                bvar((*i as i64 + by as i64) as u32)
            } else {
                e.clone()
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
        ExprData::App(f, a) => app(shift(f, by, cutoff), shift(a, by, cutoff)),
        ExprData::Lam(bi, ty, body) => lam(*bi, shift(ty, by, cutoff), shift(body, by, cutoff + 1)),
        ExprData::Pi(bi, ty, body) => pi(*bi, shift(ty, by, cutoff), shift(body, by, cutoff + 1)),
        ExprData::Let(ty, val, body) => let_(
            shift(ty, by, cutoff),
            shift(val, by, cutoff),
            shift(body, by, cutoff + 1),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, shift(v, by, cutoff)),
    }
}

/// Substitute `args` (in reverse: args[0] replaces the innermost bound var 0)
/// into `e`, which lives at binding depth `depth` (number of binders already
/// opened above the substitution site, i.e. args need to be shifted by `depth`
/// when they replace a bvar).
pub fn instantiate(e: &Expr, args: &[Expr]) -> Expr {
    instantiate_core(e, args, 0)
}

fn instantiate_core(e: &Expr, args: &[Expr], depth: u32) -> Expr {
    match &**e {
        ExprData::BVar(i) => {
            if *i >= depth && ((*i - depth) as usize) < args.len() {
                let a = &args[(*i - depth) as usize];
                shift(a, depth as i32, 0)
            } else if *i >= depth {
                bvar(*i - args.len() as u32)
            } else {
                e.clone()
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
        ExprData::App(f, a) => app(
            instantiate_core(f, args, depth),
            instantiate_core(a, args, depth),
        ),
        ExprData::Lam(bi, ty, body) => lam(
            *bi,
            instantiate_core(ty, args, depth),
            instantiate_core(body, args, depth + 1),
        ),
        ExprData::Pi(bi, ty, body) => pi(
            *bi,
            instantiate_core(ty, args, depth),
            instantiate_core(body, args, depth + 1),
        ),
        ExprData::Let(ty, val, body) => let_(
            instantiate_core(ty, args, depth),
            instantiate_core(val, args, depth),
            instantiate_core(body, args, depth + 1),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_core(v, args, depth)),
    }
}

/// Single-substitution convenience (beta / zeta): replace bvar 0 with `arg`.
pub fn instantiate1(e: &Expr, arg: &Expr) -> Expr {
    instantiate(e, std::slice::from_ref(arg))
}

pub fn instantiate_level_params(e: &Expr, subst: &rustc_hash::FxHashMap<u32, Level>) -> Expr {
    match &**e {
        ExprData::BVar(_) | ExprData::Lit(_) => e.clone(),
        ExprData::Sort(l) => sort(crate::level::instantiate(l, subst)),
        ExprData::Const(n, us) => const_(
            *n,
            us.iter()
                .map(|l| crate::level::instantiate(l, subst))
                .collect(),
        ),
        ExprData::App(f, a) => app(
            instantiate_level_params(f, subst),
            instantiate_level_params(a, subst),
        ),
        ExprData::Lam(bi, ty, body) => lam(
            *bi,
            instantiate_level_params(ty, subst),
            instantiate_level_params(body, subst),
        ),
        ExprData::Pi(bi, ty, body) => pi(
            *bi,
            instantiate_level_params(ty, subst),
            instantiate_level_params(body, subst),
        ),
        ExprData::Let(ty, val, body) => let_(
            instantiate_level_params(ty, subst),
            instantiate_level_params(val, subst),
            instantiate_level_params(body, subst),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_level_params(v, subst)),
    }
}

/// Decompose `f a1 a2 ... an` into (f, [a1..an]) (args in application order).
pub fn unfold_apps(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    loop {
        match &*cur {
            ExprData::App(f, a) => {
                args.push(a.clone());
                cur = f.clone();
            }
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level;

    #[test]
    fn intern_reuses_pointer() {
        let a = bvar(0);
        let b = bvar(0);
        assert!(Rc::ptr_eq(&a, &b));
        let f = const_(1, vec![]);
        let t1 = app(f.clone(), a.clone());
        let t2 = app(f, b);
        assert!(Rc::ptr_eq(&t1, &t2));
        let n1 = lit_nat(7u32.into());
        let n2 = lit_nat(7u32.into());
        assert!(Rc::ptr_eq(&n1, &n2));
        assert!(!Rc::ptr_eq(&n1, &lit_nat(8u32.into())));
    }

    #[test]
    fn closed_detects_loose_bvars() {
        assert!(is_closed(&const_(1, vec![])));
        assert!(is_closed(&lit_nat(0u32.into())));
        assert!(is_closed(&sort(level::zero())));
        assert!(!is_closed(&bvar(0)));
        assert!(is_closed(&lam(
            BinderInfo::Default,
            sort(level::zero()),
            bvar(0)
        )));
        assert!(!is_closed(&lam(
            BinderInfo::Default,
            sort(level::zero()),
            bvar(1)
        )));
        assert!(is_closed(&app(
            lam(BinderInfo::Default, sort(level::zero()), bvar(0)),
            const_(1, vec![])
        )));
    }
}
