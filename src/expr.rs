use crate::level::Level;
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

pub fn bvar(i: u32) -> Expr {
    Rc::new(ExprData::BVar(i))
}
pub fn sort(l: Level) -> Expr {
    Rc::new(ExprData::Sort(l))
}
pub fn const_(n: u32, us: Vec<Level>) -> Expr {
    Rc::new(ExprData::Const(n, Rc::new(us)))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    Rc::new(ExprData::App(f, a))
}
pub fn lam(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    Rc::new(ExprData::Lam(bi, ty, body))
}
pub fn pi(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    Rc::new(ExprData::Pi(bi, ty, body))
}
pub fn let_(ty: Expr, val: Expr, body: Expr) -> Expr {
    Rc::new(ExprData::Let(ty, val, body))
}
pub fn proj(s: u32, i: u32, e: Expr) -> Expr {
    Rc::new(ExprData::Proj(s, i, e))
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
            us.iter().map(|l| crate::level::instantiate(l, subst)).collect(),
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
