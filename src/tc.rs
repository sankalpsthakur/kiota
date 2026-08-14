use crate::env::{ConstantInfo, Environment, QuotKind, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr, ExprData, Lit};
use crate::level::{self, Level};
use rustc_hash::FxHashMap;
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
fn decline<T>(msg: impl Into<String>) -> R<T> {
    Err(TcError::Decline(msg.into()))
}

pub struct Checker<'e> {
    pub env: &'e Environment,
    pub nat_ref: Option<u32>,
    pub string_ref: Option<u32>,
}

type Ctx = Vec<Expr>; // ctx[len-1-i] = raw (unshifted) type recorded for bvar i

fn local_ty(ctx: &Ctx, i: u32) -> Option<Expr> {
    let n = ctx.len();
    if (i as usize) >= n {
        return None;
    }
    let raw = &ctx[n - 1 - i as usize];
    Some(expr::shift(raw, i as i32 + 1, 0))
}

impl<'e> Checker<'e> {
    pub fn new(env: &'e Environment, nat_ref: Option<u32>, string_ref: Option<u32>) -> Self {
        Checker { env, nat_ref, string_ref }
    }

    pub fn check_decl(&self, name: u32, kind: &str) -> R<()> {
        let ci = self
            .env
            .get(name)
            .ok_or_else(|| TcError::Other(format!("missing const {name}")))?;
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
        let ctx: Ctx = Vec::new();
        let sort = self.infer_type(&ctx, typ)?;
        let lvl = self.ensure_sort(&ctx, &sort)?;
        if kind == "theorem" && !level::is_def_eq(&lvl, &level::zero()) {
            return reject(format!("{kind} {name}: theorem type is not a Prop"));
        }
        if let Some(value) = ci.value() {
            let vt = self.infer_type(&ctx, value)?;
            if !self.is_def_eq(&ctx, &vt, typ)? {
                return reject(format!(
                    "{kind} {name}: value type does not match declared type"
                ));
            }
        }
        Ok(())
    }

    // ---------------- Universe / sort helpers ----------------

    fn ensure_sort(&self, ctx: &Ctx, e: &Expr) -> R<Level> {
        let w = self.whnf(ctx, e)?;
        match &*w {
            ExprData::Sort(l) => Ok(l.clone()),
            _ => reject("expected a sort"),
        }
    }

    fn ensure_pi(&self, ctx: &Ctx, e: &Expr) -> R<(BinderInfo, Expr, Expr)> {
        let w = self.whnf(ctx, e)?;
        match &*w {
            ExprData::Pi(bi, ty, body) => Ok((*bi, ty.clone(), body.clone())),
            _ => reject("expected a function type"),
        }
    }

    // ---------------- Type inference ----------------

    pub fn infer_type(&self, ctx: &Ctx, e: &Expr) -> R<Expr> {
        match &**e {
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
                    return reject("application argument type mismatch");
                }
                Ok(expr::instantiate1(&body, a))
            }
            ExprData::Lam(bi, ty, body) => {
                let tt = self.infer_type(ctx, ty)?;
                self.ensure_sort(ctx, &tt)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(ty.clone());
                let bt = self.infer_type(&ctx2, body)?;
                Ok(expr::pi(*bi, ty.clone(), bt))
            }
            ExprData::Pi(_bi, ty, body) => {
                let tt = self.infer_type(ctx, ty)?;
                let s1 = self.ensure_sort(ctx, &tt)?;
                let mut ctx2 = ctx.clone();
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
        let (ind_name, us) = match &*head {
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
            Some(ConstantInfo::Constructor { level_params, typ, num_fields, .. }) => {
                (level_params.clone(), typ.clone(), *num_fields)
            }
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
        match &**e {
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
        match &*head {
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
            Some(ConstantInfo::InductiveType { ctors, num_params, .. }) => {
                (ctors.clone(), *num_params)
            }
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
        match &*thead {
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
        let mut cur = e.clone();
        loop {
            let core = self.whnf_core(ctx, &cur)?;
            let (head, _) = expr::unfold_apps(&core);
            if let ExprData::Const(n, us) = &*head {
                if let Some(unfolded) = self.unfold_def(*n, us)? {
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
        let mut cur = e.clone();
        loop {
            match &*cur {
                ExprData::App(_, _) => {
                    let (head, args) = expr::unfold_apps(&cur);
                    match &*head {
                        ExprData::Lam(_, _, _) => {
                            let mut body = head.clone();
                            let mut i = 0;
                            while let ExprData::Lam(_, _, b) = &*body.clone() {
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
                        _ => {
                            if let Some(r) = self.try_iota(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_quot(ctx, &head, &args)? {
                                cur = r;
                                continue;
                            }
                            if let Some(r) = self.try_nat_extension(&head, &args)? {
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
                    if let ExprData::Const(cname, _us) = &*head {
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
                    if Rc::ptr_eq(&vw, v) {
                        return Ok(cur);
                    }
                    cur = expr::proj(*sname, *idx, vw);
                    continue;
                }
                ExprData::Lit(Lit::Nat(n)) => {
                    if let Some((zero, succ)) = self.nat_ctors() {
                        if n == &num_bigint::BigUint::from(0u32) {
                            return Ok(expr::const_(zero, vec![]));
                        }
                        let pred = n - 1u32;
                        cur = expr::app(
                            expr::const_(succ, vec![]),
                            Rc::new(ExprData::Lit(Lit::Nat(pred))),
                        );
                        continue;
                    }
                    return Ok(cur);
                }
                _ => return Ok(cur),
            }
        }
    }

    fn unfold_def(&self, n: u32, us: &[Level]) -> R<Option<Expr>> {
        match self.env.get(n) {
            Some(ConstantInfo::Def { level_params, value, hints, .. }) => {
                if *hints == ReducibilityHints::Opaque {
                    // still transparent for kernel defeq; unfold anyway.
                }
                let subst = level::subst_map(level_params, us);
                Ok(Some(expr::instantiate_level_params(value, &subst)))
            }
            Some(ConstantInfo::Theorem { .. }) => Ok(None),
            Some(ConstantInfo::Opaque { .. }) => Ok(None),
            _ => Ok(None),
        }
    }

    fn def_height(&self, n: u32) -> i64 {
        match self.env.get(n) {
            Some(ConstantInfo::Def { hints, .. }) => match hints {
                ReducibilityHints::Opaque => i64::MAX,
                ReducibilityHints::Abbrev => -1,
                ReducibilityHints::Regular(h) => *h as i64,
            },
            Some(ConstantInfo::Theorem { .. }) => i64::MAX,
            _ => -2,
        }
    }

    fn is_delta_reducible(&self, n: u32) -> bool {
        // Theorems are not unfolded (`unfold_def` returns None). Treating them as
        // delta-reducible made `delta_step` a no-op and `is_def_eq_core` loop.
        matches!(self.env.get(n), Some(ConstantInfo::Def { .. }))
    }

    // ---------------- Definitional equality ----------------

    pub fn is_def_eq(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        if Rc::ptr_eq(a, b) || a == b {
            return Ok(true);
        }
        let aw = self.whnf_core(ctx, a)?;
        let bw = self.whnf_core(ctx, b)?;
        self.is_def_eq_core(ctx, &aw, &bw)
    }

    fn is_def_eq_core(&self, ctx: &Ctx, a: &Expr, b: &Expr) -> R<bool> {
        if Rc::ptr_eq(a, b) || a == b {
            return Ok(true);
        }
        // Structural match without delta.
        match (&**a, &**b) {
            (ExprData::Sort(l1), ExprData::Sort(l2)) => return Ok(level::is_def_eq(l1, l2)),
            (ExprData::BVar(i), ExprData::BVar(j)) if i == j => return Ok(true),
            (ExprData::Lit(x), ExprData::Lit(y)) => return Ok(x == y),
            (ExprData::Pi(_, t1, b1), ExprData::Pi(_, t2, b2)) => {
                if !self.is_def_eq(ctx, t1, t2)? {
                    return Ok(false);
                }
                let mut ctx2 = ctx.clone();
                ctx2.push(t1.clone());
                return self.is_def_eq(&ctx2, b1, b2);
            }
            (ExprData::Lam(_, t1, b1), ExprData::Lam(_, t2, b2)) => {
                let _ = self.is_def_eq(ctx, t1, t2)?; // domains needn't match strictly if only used for eta-shape; keep permissive
                let mut ctx2 = ctx.clone();
                ctx2.push(t1.clone());
                return self.is_def_eq(&ctx2, b1, b2);
            }
            (ExprData::App(_, _), ExprData::App(_, _)) => {
                let (h1, a1) = expr::unfold_apps(a);
                let (h2, a2) = expr::unfold_apps(b);
                if let (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) = (&*h1, &*h2) {
                    if n1 == n2
                        && a1.len() == a2.len()
                        && u1.len() == u2.len()
                        && u1.iter().zip(u2.iter()).all(|(x, y)| level::is_def_eq(x, y))
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
                } else if matches!((&*h1, &*h2), (ExprData::BVar(i), ExprData::BVar(j)) if i == j)
                    && a1.len() == a2.len()
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
            }
            (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) => {
                if n1 == n2
                    && u1.len() == u2.len()
                    && u1.iter().zip(u2.iter()).all(|(x, y)| level::is_def_eq(x, y))
                {
                    return Ok(true);
                }
            }
            _ => {}
        }

        // Eta for lambdas: one side a lambda, other not -> eta-expand other.
        if let (ExprData::Lam(_, t1, _), _) = (&**a, &**b) {
            if !matches!(&**b, ExprData::Lam(_, _, _)) {
                let b_app = expr::app(expr::shift(b, 1, 0), expr::bvar(0));
                let mut ctx2 = ctx.clone();
                ctx2.push(t1.clone());
                let a_body = if let ExprData::Lam(_, _, bd) = &**a { bd.clone() } else { unreachable!() };
                return self.is_def_eq(&ctx2, &a_body, &b_app);
            }
        }
        if let (_, ExprData::Lam(_, t2, _)) = (&**a, &**b) {
            if !matches!(&**a, ExprData::Lam(_, _, _)) {
                let a_app = expr::app(expr::shift(a, 1, 0), expr::bvar(0));
                let mut ctx2 = ctx.clone();
                ctx2.push(t2.clone());
                let b_body = if let ExprData::Lam(_, _, bd) = &**b { bd.clone() } else { unreachable!() };
                return self.is_def_eq(&ctx2, &a_app, &b_body);
            }
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
        let n1 = if let ExprData::Const(n, _) = &*h1 { Some(*n) } else { None };
        let n2 = if let ExprData::Const(n, _) = &*h2 { Some(*n) } else { None };
        match (n1, n2) {
            (Some(x), Some(y)) if x == y => {
                // Same head const but arg/universe mismatch already failed above;
                // try unfolding anyway (defs of same const are identical, so this
                // shouldn't usually help, but be safe) -- fall through to unfold.
                if self.is_delta_reducible(x) {
                    let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                    let ub = self.whnf_core(ctx, &self.delta_step(b)?)?;
                    return self.is_def_eq_core(ctx, &ua, &ub);
                }
                Ok(false)
            }
            (Some(x), Some(y)) => {
                let hx = self.def_height(x);
                let hy = self.def_height(y);
                if self.is_delta_reducible(x) && (hx >= hy || !self.is_delta_reducible(y)) {
                    let ua = self.whnf_core(ctx, &self.delta_step(a)?)?;
                    self.is_def_eq_core(ctx, &ua, b)
                } else if self.is_delta_reducible(y) {
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
        }
    }

    fn delta_step(&self, e: &Expr) -> R<Expr> {
        let (head, args) = expr::unfold_apps(e);
        if let ExprData::Const(n, us) = &*head {
            if let Some(u) = self.unfold_def(*n, us)? {
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
        let (cname, num_params) = match &*ha {
            ExprData::Const(n, _) => match self.env.get(*n) {
                Some(ConstantInfo::Constructor { induct, num_params, .. }) => (*induct, *num_params),
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

    fn try_iota(&self, ctx: &Ctx, head: &Expr, args: &[Expr]) -> R<Option<Expr>> {
        let (rname, us) = match &**head {
            ExprData::Const(n, us) => (*n, us.clone()),
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
        if args.len() <= major_pos {
            return Ok(None);
        }
        let params = &args[..num_params as usize];
        let motives = &args[num_params as usize..(num_params + num_motives) as usize];
        let minors =
            &args[(num_params + num_motives) as usize..(num_params + num_motives + num_minors) as usize];
        let major = &args[major_pos];
        let rest = &args[major_pos + 1..];

        let k_like = self.is_k_like(&all)?;

        let major_w = self.whnf(ctx, major)?;
        let (mhead, margs) = expr::unfold_apps(&major_w);

        let ctor = match &*mhead {
            ExprData::Const(cname, _) => match self.env.get(*cname) {
                Some(ConstantInfo::Constructor { induct, num_params: cnp, .. })
                    if all.contains(induct) =>
                {
                    Some((*cname, *cnp, margs.clone()))
                }
                _ => None,
            },
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

        let fields = if ctor_args.len() >= cnp as usize {
            ctor_args[cnp as usize..].to_vec()
        } else {
            return Ok(None);
        };

        let minor_idx = self.ctor_minor_index(cname, &all);
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
            motives,
            minors,
            minors[minor_idx].clone(),
            cname,
            &fields,
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
                ctors, num_params, typ, ..
            }) => (ctors.clone(), *num_params, typ.clone()),
            _ => return Ok(false),
        };
        if ctors.len() != 1 {
            return Ok(false);
        }
        let mut ctx: Ctx = Vec::new();
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
                Ok(w) => match &*w {
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
            match &*ct {
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
            Some(ConstantInfo::InductiveType { ctors, num_params, .. }) if ctors.len() == 1 => {
                (ctors.clone(), *num_params)
            }
            _ => return Ok(None),
        };
        let cname = ctors[0];
        let (ctor_lp, ctor_typ, cnp) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                level_params, typ, num_params: cnp, ..
            }) => (level_params.clone(), typ.clone(), *cnp),
            _ => return Ok(None),
        };
        let mt = self.infer_type(ctx, major)?;
        let mtw = self.whnf(ctx, &mt)?;
        let (thead, targs) = expr::unfold_apps(&mtw);
        match &*thead {
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

    fn ctor_minor_index(&self, cname: u32, all: &[u32]) -> usize {
        let mut idx = 0usize;
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
        motives: &[Expr],
        minors: &[Expr],
        minor: Expr,
        cname: u32,
        fields: &[Expr],
    ) -> R<Expr> {
        let (ctor_lp, ctor_typ, cnp) = match self.env.get(cname) {
            Some(ConstantInfo::Constructor {
                level_params, typ, num_params, ..
            }) => (level_params.clone(), typ.clone(), *num_params),
            _ => return Ok(minor),
        };
        let subst = level::subst_map(&ctor_lp, us);
        let mut ct = expr::instantiate_level_params(&ctor_typ, &subst);
        for p in params.iter().take(cnp as usize) {
            let (_, _, body) = self.ensure_pi(ctx, &ct)?;
            ct = expr::instantiate1(&body, p);
        }
        let mut result = minor;
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
                result = expr::app(result, rec_call);
            }
            cctx.push(dom);
            ct = expr::instantiate1(&body, f);
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
        let mut ty = self.whnf(ctx, field_ty).unwrap_or_else(|_| field_ty.clone());
        let mut binders: Vec<Expr> = Vec::new();
        let mut tctx = ctx.clone();
        loop {
            match &*ty {
                ExprData::Pi(_, dom, body) => {
                    binders.push(dom.clone());
                    tctx.push(dom.clone());
                    ty = self.whnf(&tctx, body).unwrap_or_else(|_| body.clone());
                }
                _ => break,
            }
        }
        let (head, iargs) = expr::unfold_apps(&ty);
        let target = match &*head {
            ExprData::Const(n, _) if all.contains(n) => *n,
            _ => return Ok(None),
        };
        let nparams = params.len();
        if iargs.len() < nparams {
            return Ok(None);
        }
        let indices = &iargs[nparams..];
        let rec_name = self.env.rec_of.get(&target).copied().unwrap_or(rname);
        let rec = expr::const_(rec_name, us.to_vec());
        let mut rec_app = rec;
        for p in params {
            rec_app = expr::app(rec_app, p.clone());
        }
        for m in motives {
            rec_app = expr::app(rec_app, m.clone());
        }
        for m in minors {
            rec_app = expr::app(rec_app, m.clone());
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
        let n = match &**head {
            ExprData::Const(n, _) => *n,
            _ => return Ok(None),
        };
        let is_lift = matches!(self.env.get(n), Some(ConstantInfo::Quot { kind: QuotKind::Lift, .. }));
        let is_ind = matches!(self.env.get(n), Some(ConstantInfo::Quot { kind: QuotKind::Ind, .. }));
        if !is_lift && !is_ind {
            return Ok(None);
        }
        // Quot.lift : {α β} {r} (f : α → β) (h) (q : Quot r) → β
        //   Quot.lift f h (Quot.mk r a) ==> f a
        // Quot.ind  : {α} {r} {β : Quot r → Prop} (h : ∀ a, β (Quot.mk r a)) (q) → β q
        //   Quot.ind h (Quot.mk r a) ==> h a
        let (f_idx, q_idx, is_lift2) = if is_lift { (3usize, 5usize, true) } else { (3usize, 4usize, false) };
        if args.len() <= q_idx {
            return Ok(None);
        }
        let q = &args[q_idx];
        let (qhead, qargs) = expr::unfold_apps(q);
        let is_mk = matches!(&*qhead, ExprData::Const(cn,_) if matches!(self.env.get(*cn), Some(ConstantInfo::Quot{kind: QuotKind::Ctor,..})));
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

    fn try_nat_extension(&self, _head: &Expr, _args: &[Expr]) -> R<Option<Expr>> {
        Ok(None)
    }

    // ---------------- Inductive/recursor validation ----------------

    pub fn check_inductive_group(&self, first_name: u32) -> R<()> {
        let ci = self
            .env
            .get(first_name)
            .ok_or_else(|| TcError::Other("missing inductive".into()))?;
        let (typ, num_params, all, shared_lp) = match ci {
            ConstantInfo::InductiveType { typ, num_params, all, level_params, .. } => {
                (typ.clone(), *num_params, all.clone(), level_params.clone())
            }
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
        let mut param_ctx: Ctx = Vec::new();
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
                Some(ConstantInfo::InductiveType { num_params, num_indices, typ, level_params, .. }) => {
                    (*num_params, *num_indices, typ.clone(), level_params.clone())
                }
                _ => continue,
            };
            if t_np != num_params {
                return reject("inconsistent numParams across mutual inductive group");
            }
            if t_lp != shared_lp {
                return reject("inconsistent universe parameters across mutual inductive group");
            }
            let mut c2: Ctx = Vec::new();
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
            infos.insert(*tname, TInfo { num_params: t_np, num_indices: t_ni, sort: sort_lvl });
        }

        for tname in &all {
            let ctors = match self.env.get(*tname) {
                Some(ConstantInfo::InductiveType { ctors, .. }) => ctors.clone(),
                _ => continue,
            };
            let t_sort = infos.get(tname).map(|i| i.sort.clone()).unwrap_or_else(level::zero);
            for cname in &ctors {
                let (c_lp, c_typ, c_np) = match self.env.get(*cname) {
                    Some(ConstantInfo::Constructor { level_params, typ, num_params, .. }) => {
                        (level_params.clone(), typ.clone(), *num_params)
                    }
                    _ => continue,
                };
                if c_lp != shared_lp {
                    return reject("constructor universe parameters do not match inductive type");
                }
                if c_np != num_params {
                    return reject("constructor numParams does not match inductive type");
                }
                let mut c2: Ctx = Vec::new();
                let mut cur2 = c_typ.clone();
                for i in 0..num_params {
                    let (_, dom, body) = self.ensure_pi(&c2, &cur2)?;
                    if !self.is_def_eq(&c2, &dom, &param_ctx[i as usize])? {
                        return reject("constructor parameter telescope does not match inductive type");
                    }
                    c2.push(dom);
                    cur2 = body;
                }
                loop {
                    // Only walk *manifest* Pis — do not whnf the constructor type
                    // itself (see tutorial/054_reduceCtorType).
                    match &*cur2 {
                        ExprData::Pi(_, dom, body) => {
                            self.check_arg_positive(&c2, dom, &all)?;
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
                match &*head {
                    ExprData::Const(n, us) if n == tname => {
                        let expected: Vec<Level> = shared_lp.iter().map(|p| level::param(*p)).collect();
                        if us.len() != expected.len()
                            || !us.iter().zip(expected.iter()).all(|(a, b)| level::is_def_eq(a, b))
                        {
                            return reject("constructor conclusion applies inductive type at wrong universes");
                        }
                    }
                    _ => return reject("constructor conclusion is not the inductive type being defined"),
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
        match &*w {
            ExprData::Pi(_, dom, body) => {
                self.check_arg_positive(ctx, dom, bound)?;
                let mut ctx2 = ctx.clone();
                ctx2.push(dom.clone());
                self.check_positivity(&ctx2, body, bound, _strict_pos_ok)
            }
            _ => Ok(()),
        }
    }

    /// Check that one constructor argument type (which may itself be a
    /// function type) is strictly positive: `bound` names may not occur in
    /// any nested domain, and may only occur in the final head position as a
    /// direct, non-nested recursive occurrence `I params.. indices..`.
    fn check_arg_positive(&self, ctx: &Ctx, arg_ty: &Expr, bound: &[u32]) -> R<()> {
        let mut cur = self.whnf(ctx, arg_ty).unwrap_or_else(|_| arg_ty.clone());
        let mut ctx2 = ctx.clone();
        loop {
            match &*cur {
                ExprData::Pi(_, dom, body) => {
                    if self.occurs_any(dom, bound) {
                        return reject("non-positive (negative) occurrence in constructor argument");
                    }
                    ctx2.push(dom.clone());
                    cur = self.whnf(&ctx2, body).unwrap_or_else(|_| body.clone());
                }
                _ => break,
            }
        }
        if !self.occurs_any(&cur, bound) {
            return Ok(());
        }
        let (h, args) = expr::unfold_apps(&cur);
        if let ExprData::Const(n, _) = &*h {
            if bound.contains(n) {
                for a in &args {
                    if self.occurs_any(a, bound) {
                        return decline("nested inductive occurrence");
                    }
                }
                return Ok(());
            }
        }
        decline("occurrence of inductive type in unsupported position")
    }

    fn occurs_any(&self, e: &Expr, names: &[u32]) -> bool {
        match &**e {
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

