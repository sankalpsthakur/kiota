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

/// An interned node: the term itself plus the one derived fact the hot paths
/// need constantly. `loose` is the smallest `k` such that every loose bvar in
/// the node has index `< k` (0 = closed). It is computed once at intern time
/// from the children's own `loose` values, so reading it is a field load rather
/// than a traversal or a hash lookup.
pub struct ExprNode {
    data: ExprData,
    loose: u32,
}

impl std::ops::Deref for ExprNode {
    type Target = ExprData;
    #[inline(always)]
    fn deref(&self) -> &ExprData {
        &self.data
    }
}

impl std::fmt::Debug for ExprNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

// Every node is created through `intern`, which returns the existing
// allocation for a structurally equal node. So identity is address equality,
// and that is already the invariant `node_eq` relies on for children.
impl PartialEq for ExprNode {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for ExprNode {}
impl Hash for ExprNode {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self as *const ExprNode as usize).hash(state)
    }
}

pub type Expr = Rc<ExprNode>;

fn ptr(e: &Expr) -> usize {
    Rc::as_ptr(e) as usize
}

/// The smallest `k` such that every loose bvar in `e` has index `< k`.
/// Zero means `e` is closed.
///
/// This is the quantity that makes eager substitution affordable: a subterm
/// whose range is `<= depth` cannot be touched by a substitution at `depth`,
/// so `instantiate`/`shift` can return it whole instead of rebuilding it.
#[inline(always)]
pub fn loose_bvar_range(e: &Expr) -> u32 {
    e.loose
}

/// Computed once per node, from children that already carry their own range.
fn loose_of(d: &ExprData) -> u32 {
    match d {
        ExprData::BVar(i) => *i + 1,
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => 0,
        ExprData::App(f, a) => f.loose.max(a.loose),
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            ty.loose.max(body.loose.saturating_sub(1))
        }
        ExprData::Let(ty, val, body) => ty.loose.max(val.loose).max(body.loose.saturating_sub(1)),
        ExprData::Proj(_, _, v) => v.loose,
    }
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
        let loose = loose_of(&d);
        let e = Rc::new(ExprNode { data: d, loose });
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

/// True when `e` has no loose bvars.
#[inline(always)]
pub fn is_closed(e: &Expr) -> bool {
    e.loose == 0
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
    // Every loose bvar is below the cutoff, so nothing here moves.
    if loose_bvar_range(e) <= cutoff {
        return e.clone();
    }
    crate::stats::shift_node();
    match &***e {
        ExprData::BVar(i) => {
            if *i >= cutoff {
                bvar((*i as i64 + by as i64) as u32)
            } else {
                e.clone()
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
        ExprData::App(_, _) => {
            let (head, args_app) = unfold_apps(e);
            let mut result = shift(&head, by, cutoff);
            for a in &args_app {
                result = app(result, shift(a, by, cutoff));
            }
            result
        }
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
    // Proof bodies are DAG-shared through the interner: the same subterm
    // reaches many occurrences, and without a memo each occurrence pays a
    // full traversal. The grind perf tests amplify a shared simp-lemma
    // application thousands of times; keying on (node, depth) — args are
    // fixed within one call — visits each unique node once.
    crate::stats::inst_call();
    let mut memo = rustc_hash::FxHashMap::default();
    instantiate_core(e, args, 0, &mut memo)
}

fn instantiate_core(
    e: &Expr,
    args: &[Expr],
    depth: u32,
    memo: &mut rustc_hash::FxHashMap<(usize, u32), Expr>,
) -> Expr {
    // Every loose bvar is bound above `depth`, so neither the substitution nor
    // the renumbering below can reach into this subterm. Returning it whole is
    // what turns O(term size) per binder into O(path length).
    if loose_bvar_range(e) <= depth {
        crate::stats::inst_skip();
        return e.clone();
    }
    let key = (Rc::as_ptr(e) as usize, depth);
    if let Some(r) = memo.get(&key) {
        crate::stats::inst_memo_hit();
        return r.clone();
    }
    crate::stats::inst_node();
    let r = match &***e {
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
        ExprData::App(_, _) => {
            let (head, args_app) = unfold_apps(e);
            let mut result = instantiate_core(&head, args, depth, memo);
            for a in &args_app {
                result = app(result, instantiate_core(a, args, depth, memo));
            }
            result
        }
        ExprData::Lam(bi, ty, body) => lam(
            *bi,
            instantiate_core(ty, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Pi(bi, ty, body) => pi(
            *bi,
            instantiate_core(ty, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Let(ty, val, body) => let_(
            instantiate_core(ty, args, depth, memo),
            instantiate_core(val, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_core(v, args, depth, memo)),
    };
    memo.insert(key, r.clone());
    r
}

/// Single-substitution convenience (beta / zeta): replace bvar 0 with `arg`.
pub fn instantiate1(e: &Expr, arg: &Expr) -> Expr {
    instantiate(e, std::slice::from_ref(arg))
}

pub fn instantiate_level_params(e: &Expr, subst: &rustc_hash::FxHashMap<u32, Level>) -> Expr {
    match &***e {
        ExprData::BVar(_) | ExprData::Lit(_) => e.clone(),
        ExprData::Sort(l) => sort(crate::level::instantiate(l, subst)),
        ExprData::Const(n, us) => const_(
            *n,
            us.iter()
                .map(|l| crate::level::instantiate(l, subst))
                .collect(),
        ),
        ExprData::App(_, _) => {
            let (head, args_app) = unfold_apps(e);
            let mut result = instantiate_level_params(&head, subst);
            for a in &args_app {
                result = app(result, instantiate_level_params(a, subst));
            }
            result
        }
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
        match &**cur {
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

    fn s0() -> Expr {
        sort(level::zero())
    }

    #[test]
    fn loose_range_counts_the_highest_free_index() {
        assert_eq!(loose_bvar_range(&bvar(0)), 1);
        assert_eq!(loose_bvar_range(&bvar(3)), 4);
        assert_eq!(loose_bvar_range(&const_(1, vec![])), 0);
        // A binder discharges exactly one level.
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, s0(), bvar(0))),
            0
        );
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, s0(), bvar(2))),
            2
        );
        // The binder does not cover the domain, only the body.
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, bvar(4), bvar(0))),
            5
        );
        assert_eq!(
            loose_bvar_range(&app(bvar(1), bvar(6))),
            7,
            "app takes the max of both sides"
        );
        assert_eq!(
            loose_bvar_range(&let_(bvar(2), bvar(1), bvar(3))),
            3,
            "only the let body is under the binder"
        );
        assert_eq!(loose_bvar_range(&proj(0, 0, bvar(5))), 6);
    }

    /// Reference substitution with no short-circuit, used to prove the fast
    /// path in `instantiate_core` never changes a result.
    fn instantiate_ref(e: &Expr, args: &[Expr], depth: u32) -> Expr {
        match &***e {
            ExprData::BVar(i) => {
                if *i >= depth && ((*i - depth) as usize) < args.len() {
                    shift_ref(&args[(*i - depth) as usize], depth as i32, 0)
                } else if *i >= depth {
                    bvar(*i - args.len() as u32)
                } else {
                    e.clone()
                }
            }
            ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
            ExprData::App(f, a) => app(
                instantiate_ref(f, args, depth),
                instantiate_ref(a, args, depth),
            ),
            ExprData::Lam(bi, ty, b) => lam(
                *bi,
                instantiate_ref(ty, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Pi(bi, ty, b) => pi(
                *bi,
                instantiate_ref(ty, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Let(ty, v, b) => let_(
                instantiate_ref(ty, args, depth),
                instantiate_ref(v, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_ref(v, args, depth)),
        }
    }

    fn shift_ref(e: &Expr, by: i32, cutoff: u32) -> Expr {
        if by == 0 {
            return e.clone();
        }
        match &***e {
            ExprData::BVar(i) => {
                if *i >= cutoff {
                    bvar((*i as i64 + by as i64) as u32)
                } else {
                    e.clone()
                }
            }
            ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
            ExprData::App(f, a) => app(shift_ref(f, by, cutoff), shift_ref(a, by, cutoff)),
            ExprData::Lam(bi, ty, b) => {
                lam(*bi, shift_ref(ty, by, cutoff), shift_ref(b, by, cutoff + 1))
            }
            ExprData::Pi(bi, ty, b) => {
                pi(*bi, shift_ref(ty, by, cutoff), shift_ref(b, by, cutoff + 1))
            }
            ExprData::Let(ty, v, b) => let_(
                shift_ref(ty, by, cutoff),
                shift_ref(v, by, cutoff),
                shift_ref(b, by, cutoff + 1),
            ),
            ExprData::Proj(s, i, v) => proj(*s, *i, shift_ref(v, by, cutoff)),
        }
    }

    /// Deterministic pseudo-random terms over a small alphabet, deep enough to
    /// exercise nested binders and every node kind.
    fn gen(seed: &mut u64, depth: u32) -> Expr {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = (*seed >> 33) % if depth == 0 { 3 } else { 8 };
        match pick {
            0 => bvar((*seed >> 13) as u32 % 6),
            1 => const_((*seed >> 17) as u32 % 3, vec![]),
            2 => s0(),
            3 => app(gen(seed, depth - 1), gen(seed, depth - 1)),
            4 => lam(
                BinderInfo::Default,
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            5 => pi(
                BinderInfo::Default,
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            6 => let_(
                gen(seed, depth - 1),
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            _ => proj(0, 0, gen(seed, depth - 1)),
        }
    }

    #[test]
    fn short_circuit_never_changes_substitution() {
        let mut seed = 0x5EED_1234_u64;
        for _ in 0..400 {
            let e = gen(&mut seed, 5);
            let a0 = gen(&mut seed, 3);
            let a1 = gen(&mut seed, 3);
            for args in [vec![a0.clone()], vec![a0.clone(), a1.clone()]] {
                assert!(
                    Rc::ptr_eq(&instantiate(&e, &args), &instantiate_ref(&e, &args, 0)),
                    "instantiate diverged from the reference"
                );
            }
            for cutoff in 0..4u32 {
                assert!(
                    Rc::ptr_eq(&shift(&e, 2, cutoff), &shift_ref(&e, 2, cutoff)),
                    "shift diverged from the reference at cutoff {cutoff}"
                );
            }
        }
    }
}
