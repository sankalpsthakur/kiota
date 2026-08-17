use crate::env::{ConstantInfo, Environment, QuotKind, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr, ExprData, Lit};
use crate::level::{self, Level};
use crate::nat;
use num_bigint::{BigInt, BigUint, Sign};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;

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
    fn gcd_64_then_0() {
        assert_eq!(
            num_bigint_gcd(&BigUint::from(64u32), &BigUint::from(0u32)),
            BigUint::from(64u32)
        );
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
    defeq_cache: RefCell<FxHashMap<(usize, usize), bool>>,
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
    /// `Nat.rec` peels of literals with `bits() >= 20` (`hugeFuel = 1e6`).
    fuel_nat_peels: std::cell::Cell<u32>,
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
            unfold_cache: RefCell::new(FxHashMap::default()),
            fuel_nat_peels: std::cell::Cell::new(0),
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
        self.fuel_nat_peels.set(0);
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

    fn ensure_sort(&self, ctx: &Ctx, e: &Expr) -> R<Level> {
        let w = self.whnf(ctx, e)?;
        match &**w {
            ExprData::Sort(l) => Ok(l.clone()),
            _ => reject("expected a sort"),
        }
    }

    fn ensure_pi(&self, ctx: &Ctx, e: &Expr) -> R<(BinderInfo, Expr, Expr)> {
        let w = self.whnf(ctx, e)?;
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
            // Collect constructor field telescope (un-instantiated) to find the
            // first *dependent* data field — a Type field mentioned by a later
            // field. Projections at later indices are forbidden.
            let mut teles = {
                let subst2 = level::subst_map(&ctor_lp, &us);
                let mut t = expr::instantiate_level_params(&ctor_typ, &subst2);
                for p in args.iter().take(num_params as usize) {
                    let (_, _, body) = self.ensure_pi(ctx, &t)?;
                    t = expr::instantiate1(&body, p);
                }
                t
            };
            let mut ftypes: Vec<Expr> = Vec::new();
            let mut fctx = ctx.clone();
            for _ in 0..num_fields {
                let (_, d, body) = self.ensure_pi(&fctx, &teles)?;
                ftypes.push(d.clone());
                fctx.push(d.clone());
                teles = body;
            }
            let mut first_dep: Option<u32> = None;
            for i in 0..num_fields as usize {
                if self.is_prop(&ctx, &ftypes[i]).unwrap_or(false) {
                    continue;
                }
                let mut used = false;
                for j in (i + 1)..ftypes.len() {
                    let bv = (j - 1 - i) as u32;
                    if Self::occurs_bvar(&ftypes[j], bv) {
                        used = true;
                        break;
                    }
                }
                if used {
                    first_dep = Some(i as u32);
                    break;
                }
            }
            if let Some(d) = first_dep {
                if idx > d {
                    return reject("projection after a dependent data field of a Prop structure");
                }
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
        match self.infer_type(ctx, ty) {
            Ok(s) => match self.ensure_sort(ctx, &s) {
                Ok(l) => Ok(level::is_def_eq(&l, &level::zero())),
                Err(_) => Ok(false),
            },
            Err(_) => Ok(false),
        }
    }

    // ---------------- Reduction ----------------

    pub fn whnf(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
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
                if let Some(unfolded) = self.unfold_def(*n, us)? {
                    let (_, args) = expr::unfold_apps(&core);
                    cur = expr::apps(unfolded, &args);
                    continue;
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

    /// WHNF plus cheap delta: abbrevs and low-height defs (`ctorIdx`,
    /// `casesOn`). Does not unfold `brecOn` helpers such as `modCore.go`.
    fn whnf_for_defeq(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        self.whnf(ctx, e)
    }

    /// WHNF for recursor major premises: like `whnf`, but delta-unfolds
    /// theorem values too (via `unfold_delta`). Lean's kernel unfolds any
    /// constant with a value — theorems included — when it needs the
    /// constructor of a `rec` major premise; without this, majors headed by
    /// a theorem (e.g. `Acc.inv … x h` well-founded recursion proofs, or
    /// `_proof` lemmas wrapping `Acc.intro`) never reach a constructor and
    /// the iota rule never fires. Kept off the hot `whnf` path: only the
    /// major-premise position of a recursor pays for theorem unfolding.
    fn whnf_major(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        let mut cur = e.clone();
        loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            if let ExprData::Const(n, us) = &**head {
                if let Some(unfolded) = self.unfold_delta(*n, us)? {
                    let (_, args) = expr::unfold_apps(&core);
                    cur = expr::apps(unfolded, &args);
                    continue;
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
    fn unfold_delta(&self, n: u32, us: &[Level]) -> R<Option<Expr>> {
        if let Some(r) = self.unfold_def(n, us)? {
            return Ok(Some(r));
        }
        if std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_some()
            || !crate::stats::theorem_delta_in_scope()
        {
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
        let is_thm = matches!(self.env.get(n), Some(ConstantInfo::Theorem { .. }))
            && std::env::var_os("KIOTA_NO_THEOREM_DELTA").is_none()
            && crate::stats::theorem_delta_in_scope();
        matches!(self.env.get(n), Some(ConstantInfo::Def { .. })) || is_thm
    }

    // ---------------- Definitional equality ----------------

    pub fn is_def_eq(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
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
        let key = (min_k, max_k);
        if let Some(&r) = self.defeq_cache.borrow().get(&key) {
            return Ok(r);
        }
        let aw = self.whnf_for_defeq(ctx, a)?;
        let bw = self.whnf_for_defeq(ctx, b)?;
        let r = self.is_def_eq_core(ctx, &aw, &bw)?;
        self.defeq_cache.borrow_mut().insert(key, r);
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
        if let Some((zero, succ)) = self.nat_ctors() {
            if let (Some(x), Some(y)) = (
                nat::numeral_value(a, zero, succ),
                nat::numeral_value(b, zero, succ),
            ) {
                return Ok(x == y);
            }
        }
        let (h1, _) = expr::unfold_apps(a);
        if let ExprData::Const(n, _) = &**h1 {
            if matches!(self.env.get(*n), Some(ConstantInfo::Theorem { .. })) {
                if let Ok(ta) = self.infer_type(ctx, a) {
                    if self.is_prop(ctx, &ta)? {
                        if let Ok(tb) = self.infer_type(ctx, b) {
                            if self.is_def_eq(ctx, &ta, &tb)? {
                                return Ok(true);
                            }
                        }
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
                        let mut all = true;
                        for (x, y) in a1.iter().zip(a2.iter()) {
                            if !self.is_def_eq(ctx, x, y)? {
                                all = false;
                                break;
                            }
                        }
                        if all {
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
                        let mut all = true;
                        for (x, y) in a1.iter().zip(a2.iter()) {
                            if !self.is_def_eq(ctx, x, y)? {
                                all = false;
                                break;
                            }
                        }
                        if all {
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
                // Same head const but arg/universe mismatch already failed above;
                // try unfolding anyway (defs of same const are identical, so this
                // shouldn't usually help, but be safe) -- fall through to unfold.
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
        if let Ok(ta) = self.infer_type(ctx, a) {
            if self.is_prop(ctx, &ta)? {
                if let Ok(tb) = self.infer_type(ctx, b) {
                    if self.is_def_eq(ctx, &ta, &tb)? {
                        return Ok(true);
                    }
                }
            }
        }

        Ok(false)
    }

    fn delta_step(&self, e: &Expr) -> R<Expr> {
        let (head, args) = expr::unfold_apps(e);
        if let ExprData::Const(n, us) = &**head {
            if let Some(u) = self.unfold_delta(*n, us)? {
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

    /// `Poly.cancelAux hugeFuel` (`1e6`, 20 bits) needs O(|poly|) peels.
    /// A million-step countdown of that fuel is the `#3256` hang; keep
    /// this well above typical poly length and well below `1e6`.
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

        let major_w = self.whnf_major(ctx, major)?;
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
                    if nat_induct.map(|ind| all.contains(&ind)).unwrap_or(false) || rec_owns_ctor(zero) {
                        if n == &num_bigint::BigUint::from(0u32) {
                            Some((zero, 0, vec![]))
                        } else if n.bits() > 24 {
                            // `UInt32.toNat_shiftLeft` peels `2^32` (33 bits).
                            None
                        } else if n.bits() >= 20 {
                            // `hugeFuel = 1_000_000`. `cancelAux` needs
                            // O(|poly|) successor peels; `#3256` counted
                            // the fuel down by tens of thousands and
                            // filled RAM. Do not cap 16–19 bit peels
                            // here: `assemble₂._proof_2` needs those.
                            let used = self.fuel_nat_peels.get();
                            if used >= Self::FUEL_NAT_LIT_PEEL_MAX {
                                None
                            } else {
                                self.fuel_nat_peels.set(used + 1);
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
        for (i, bty) in binders.iter().enumerate().rev() {
            let shifted = expr::shift(bty, i as i32, 0);
            rec_app = expr::lam(crate::expr::BinderInfo::Default, shifted, rec_app);
        }
        Ok(Some(rec_app))
    }

    fn try_quot(&self, _ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
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
        let q = &args[q_idx];
        let (qhead, qargs) = expr::unfold_apps(q);
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
            "Int.sub" if args.len() >= 2 => {
                let a = self.whnf(ctx, &args[0])?;
                let b = self.whnf(ctx, &args[1])?;
                // Only closed numerals — `Int.zero_sub` needs `0 - n` to stay
                // a `sub` so its recursor motive matches.
                if self.is_int_of_nat_zero(&a) && self.is_closed_int_numeral(&b) {
                    if let Some(ineg) = self.find_name_ending("Int.neg") {
                        let r = expr::app(expr::const_(ineg, vec![]), b);
                        return Ok(Some(expr::apps(r, &args[2..])));
                    }
                }
                Ok(None)
            }
            "Int.neg" if !args.is_empty() => {
                // Only when the argument is ≤ 0, so the result is a
                // non-negative `OfNat`. Negating a positive OfNat would
                // rebuild `Int.neg (OfNat n)` and loop in WHNF.
                if let Some(v) = self.closed_int_value(ctx, &args[0])? {
                    if v.sign() != Sign::Plus {
                        if let Some(r) = self.mk_closed_int(&-v) {
                            return Ok(Some(expr::apps(r, &args[1..])));
                        }
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
                stripped[0] = ty;
                if let Some(v) = nat::of_nat_value(&stripped, nat_ty) {
                    return Ok(Some(expr::apps(v, &args[3..])));
                }
                if let Some(v) = nat::of_nat_value(args, nat_ty) {
                    return Ok(Some(expr::apps(v, &args[3..])));
                }
                Ok(None)
            }
            _ => Ok(None),
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
        Ok(None)
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
}
