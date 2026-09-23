//! Reconstruct recursor signatures from checked inductive declarations.
//!
//! The reference algorithm is Lean 4.33.0's `src/kernel/inductive.cpp`:
//! - [base construction](https://github.com/leanprover/lean4/blob/v4.33.0/src/kernel/inductive.cpp#L478-L790):
//!   `init_elim_level`, `mk_rec_infos`, and `declare_recursors` determine
//!   universes and the parameter/motive/minor/index/major/result telescope;
//! - [nested construction](https://github.com/leanprover/lean4/blob/v4.33.0/src/kernel/inductive.cpp#L797-L1259):
//!   nested occurrences expand breadth-first into a mutual group, then
//!   `restore_nested` and `mk_aux_rec_name_map` restore exported signatures.
//!
//! Here `RecMember` represents each auxiliary member directly in restored
//! form: its source inductive plus fixed specialization parameters. This avoids
//! installing temporary declarations, while preserving Lean's discovery and
//! minor-premise order. Binder types use de Bruijn indices in the context of
//! preceding binders; `close_rec_telescope` closes them from right to left.
//!
//! Construction never looks up a supplied current-block recursor. The parser
//! first checks the types and constructors, then compares closed supplied
//! signatures up to positional universe renaming and definitional equality.
//! Only reconstructed signatures become available to later declarations.

use super::{reject, Checker, Ctx, R, TcError};
use crate::env::ConstantInfo;
use crate::expr::{self, BinderInfo, Expr, ExprData};
use crate::level::{self, Level};
use rustc_hash::FxHashMap;
use std::rc::Rc;

/// A recursor declaration reconstructed from the inductive declarations in
/// the current environment.  In particular, `typ` and every count here are
/// derived; the parser must never copy their serialized counterparts into the
/// environment.  The parser supplies the declaration name and rules only
/// after it has compared the supplied type with `typ` and checked the rules.
#[derive(Clone, Debug)]
pub(crate) struct DerivedRecursor {
    pub typ: Expr,
    pub level_params: Vec<u32>,
    pub all: Vec<u32>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub k: bool,
}

/// A binder whose type is expressed in the context formed by the preceding
/// entries.  Closing this list in reverse is the only place the recursor
/// builder manufactures Pi nodes; callers therefore never need to guess a
/// de Bruijn index while closing a telescope.
#[derive(Clone)]
struct RecBinder {
    info: BinderInfo,
    typ: Expr,
}

/// A constructor in the semantic (possibly nested-expanded) mutual group.
/// `typ` has the current declaration's shared parameter telescope, even when
/// the constructor was copied from a prior inductive at a specialization whose
/// own parameter count differs.  `name` and `levels` are the restored source
/// constructor, so no temporary auxiliary declaration ever enters the
/// checker environment.
#[derive(Clone)]
struct RecConstructor {
    name: u32,
    levels: Vec<Level>,
    typ: Expr,
}

/// One member of Lean's auxiliary mutual group, represented directly in its
/// restored form.  For an original member, `fixed_params` are the current
/// declaration parameters.  For a nested member copied from `source_name`,
/// they are the prior inductive specialization which caused that member to be
/// copied.  Every expression in `fixed_params` lives in the canonical context
/// containing exactly the current declaration parameters.
#[derive(Clone)]
struct RecMember {
    source_name: u32,
    source_levels: Vec<Level>,
    fixed_params: Vec<Expr>,
    typ: Expr,
    num_indices: u32,
    ctors: Vec<RecConstructor>,
}

struct NestedOccurrence {
    source_name: u32,
    source_levels: Vec<Level>,
    fixed_params: Vec<Expr>,
    source_all: Vec<u32>,
    source_num_params: u32,
}

fn close_rec_telescope(binders: &[RecBinder], mut result: Expr) -> Expr {
    for b in binders.iter().rev() {
        result = expr::pi(b.info, b.typ.clone(), result);
    }
    result
}

fn ids_are_pairwise_distinct(ids: &[u32]) -> bool {
    let mut seen = Vec::with_capacity(ids.len());
    for id in ids {
        if seen.contains(id) {
            return false;
        }
        seen.push(*id);
    }
    true
}

/// `ExprNode::eq` is intentionally pointer identity because the live interner
/// normally canonicalizes nodes.  Environment expressions can outlive an
/// interner clear, though, so nested-specialization keys need an explicit
/// structural comparison rather than assuming both terms came from the same
/// interner generation.
fn rec_expr_eq(a: &Expr, b: &Expr) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    match (&***a, &***b) {
        (ExprData::BVar(i), ExprData::BVar(j)) => i == j,
        (ExprData::Sort(u), ExprData::Sort(v)) => u == v,
        (ExprData::Const(n, us), ExprData::Const(m, vs)) => n == m && us == vs,
        (ExprData::App(f, x), ExprData::App(g, y)) => rec_expr_eq(f, g) && rec_expr_eq(x, y),
        (ExprData::Lam(bi, ty, body), ExprData::Lam(bj, ty2, body2))
        | (ExprData::Pi(bi, ty, body), ExprData::Pi(bj, ty2, body2)) => {
            bi == bj && rec_expr_eq(ty, ty2) && rec_expr_eq(body, body2)
        }
        (ExprData::Let(ty, val, body), ExprData::Let(ty2, val2, body2)) => {
            rec_expr_eq(ty, ty2) && rec_expr_eq(val, val2) && rec_expr_eq(body, body2)
        }
        (ExprData::Proj(s, i, v), ExprData::Proj(t, j, w)) => {
            s == t && i == j && rec_expr_eq(v, w)
        }
        (ExprData::Lit(x), ExprData::Lit(y)) => x == y,
        _ => false,
    }
}

fn rec_exprs_eq(a: &[Expr], b: &[Expr]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| rec_expr_eq(x, y))
}

fn has_bvar_in_range(e: &Expr, lo: u32, hi: u32, inner: u32) -> bool {
    match &***e {
        ExprData::BVar(i) => *i >= inner + lo && *i < inner + hi,
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => false,
        ExprData::App(f, a) => {
            has_bvar_in_range(f, lo, hi, inner) || has_bvar_in_range(a, lo, hi, inner)
        }
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            has_bvar_in_range(ty, lo, hi, inner)
                || has_bvar_in_range(body, lo, hi, inner + 1)
        }
        ExprData::Let(ty, val, body) => {
            has_bvar_in_range(ty, lo, hi, inner)
                || has_bvar_in_range(val, lo, hi, inner)
                || has_bvar_in_range(body, lo, hi, inner + 1)
        }
        ExprData::Proj(_, _, v) => has_bvar_in_range(v, lo, hi, inner),
    }
}

fn collect_level_ids_level(l: &Level, out: &mut Vec<u32>) {
    match &**l {
        crate::level::LevelData::Zero => {}
        crate::level::LevelData::Succ(a) => collect_level_ids_level(a, out),
        crate::level::LevelData::Max(a, b) | crate::level::LevelData::IMax(a, b) => {
            collect_level_ids_level(a, out);
            collect_level_ids_level(b, out);
        }
        crate::level::LevelData::Param(id) => {
            if !out.contains(id) {
                out.push(*id);
            }
        }
    }
}

fn collect_level_ids_expr(e: &Expr, out: &mut Vec<u32>) {
    match &***e {
        ExprData::BVar(_) | ExprData::Lit(_) => {}
        ExprData::Sort(l) => collect_level_ids_level(l, out),
        ExprData::Const(_, ls) => {
            for l in ls.iter() {
                collect_level_ids_level(l, out);
            }
        }
        ExprData::App(f, a) => {
            collect_level_ids_expr(f, out);
            collect_level_ids_expr(a, out);
        }
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            collect_level_ids_expr(ty, out);
            collect_level_ids_expr(body, out);
        }
        ExprData::Let(ty, val, body) => {
            collect_level_ids_expr(ty, out);
            collect_level_ids_expr(val, out);
            collect_level_ids_expr(body, out);
        }
        ExprData::Proj(_, _, v) => collect_level_ids_expr(v, out),
    }
}

impl<'e> Checker<'e> {
    fn rec_params(
        &self,
        first_typ: &Expr,
        num_params: u32,
        level_subst: &FxHashMap<u32, Level>,
    ) -> R<Vec<RecBinder>> {
        let mut ctx = Ctx::new();
        let mut cur = expr::instantiate_level_params(first_typ, level_subst);
        let mut params = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            let (bi, dom, body) = self.ensure_pi(&ctx, &cur)?;
            params.push(RecBinder {
                info: bi,
                typ: dom.clone(),
            });
            ctx.push(dom);
            cur = body;
        }
        Ok(params)
    }

    fn original_rec_members(
        &self,
        all: &[u32],
        num_params: u32,
        level_subst: &FxHashMap<u32, Level>,
        decl_levels: &[Level],
    ) -> R<Vec<RecMember>> {
        let fixed_params: Vec<Expr> = (0..num_params as usize)
            .map(|i| expr::bvar((num_params as usize - 1 - i) as u32))
            .collect();
        let mut members = Vec::with_capacity(all.len());
        for tname in all {
            let (typ, num_indices, ctor_names) = match self.env.get(*tname) {
                Some(ConstantInfo::InductiveType {
                    typ,
                    num_indices,
                    ctors,
                    ..
                }) => (
                    expr::instantiate_level_params(typ, level_subst),
                    *num_indices,
                    ctors.clone(),
                ),
                _ => return reject("missing original inductive during recursor reconstruction"),
            };
            let mut ctors = Vec::with_capacity(ctor_names.len());
            for cname in ctor_names {
                let ctyp = match self.env.get(cname) {
                    Some(ConstantInfo::Constructor { typ, .. }) => {
                        expr::instantiate_level_params(typ, level_subst)
                    }
                    _ => return reject("missing original constructor during recursor reconstruction"),
                };
                ctors.push(RecConstructor {
                    name: cname,
                    levels: decl_levels.to_vec(),
                    typ: ctyp,
                });
            }
            members.push(RecMember {
                source_name: *tname,
                source_levels: decl_levels.to_vec(),
                fixed_params: fixed_params.clone(),
                typ,
                num_indices,
                ctors,
            });
        }
        if members.iter().any(|m| m.fixed_params.len() != num_params as usize) {
            return Err(TcError::Other("original recursor parameter arity changed".into()));
        }
        Ok(members)
    }

    fn specialize_prior_telescope(
        &self,
        typ: &Expr,
        prior_level_params: &[u32],
        occurrence_levels: &[Level],
        prior_num_params: u32,
        fixed_params: &[Expr],
        current_params: &[RecBinder],
    ) -> R<Expr> {
        if prior_level_params.len() != occurrence_levels.len()
            || fixed_params.len() != prior_num_params as usize
        {
            return reject("nested inductive specialization has the wrong arity");
        }
        let subst = level::subst_map(prior_level_params, occurrence_levels);
        let mut cur = expr::instantiate_level_params(typ, &subst);
        let mut ctx = Ctx::new();
        for _ in 0..prior_num_params {
            let (_, dom, body) = self.ensure_pi(&ctx, &cur)?;
            ctx.push(dom);
            cur = body;
        }
        let reverse_params: Vec<Expr> = fixed_params.iter().rev().cloned().collect();
        let body = expr::instantiate(&cur, &reverse_params);
        Ok(close_rec_telescope(current_params, body))
    }

    fn member_prefix_matches_at_depth(
        &self,
        member: &RecMember,
        e: &Expr,
        current_num_params: u32,
        total_depth: usize,
    ) -> Option<Vec<Expr>> {
        let (head, args) = expr::unfold_apps(e);
        let ExprData::Const(n, levels) = &**head else {
            return None;
        };
        if *n != member.source_name
            || levels.as_slice() != member.source_levels.as_slice()
            || args.len() < member.fixed_params.len()
            || total_depth < current_num_params as usize
        {
            return None;
        }
        let shift_by = (total_depth - current_num_params as usize) as i32;
        for (actual, fixed) in args.iter().zip(member.fixed_params.iter()) {
            if !rec_expr_eq(actual, &expr::shift(fixed, shift_by, 0)) {
                return None;
            }
        }
        Some(args[member.fixed_params.len()..].to_vec())
    }

    fn member_matches_at_depth(
        &self,
        member: &RecMember,
        e: &Expr,
        current_num_params: u32,
        total_depth: usize,
    ) -> Option<Vec<Expr>> {
        let indices = self.member_prefix_matches_at_depth(
            member,
            e,
            current_num_params,
            total_depth,
        )?;
        (indices.len() == member.num_indices as usize).then_some(indices)
    }

    fn find_member_target(
        &self,
        members: &[RecMember],
        e: &Expr,
        current_num_params: u32,
        total_depth: usize,
    ) -> Option<(usize, Vec<Expr>)> {
        members.iter().enumerate().find_map(|(i, member)| {
            self.member_matches_at_depth(member, e, current_num_params, total_depth)
                .map(|indices| (i, indices))
        })
    }

    fn find_member_target_defeq(
        &self,
        members: &[RecMember],
        e: &Expr,
        current_num_params: u32,
        ctx: &Ctx,
    ) -> R<Option<(usize, Vec<Expr>)>> {
        // A recursive target may be hidden behind an ordinary reducible
        // definition such as `constType`.  Normalize before inspecting the
        // application head, then retain the same exact member/arity and
        // contextual parameter checks below.  Failure to normalize remains
        // fail-closed through `whnf`'s error.
        let normalized = self.whnf(ctx, e)?;
        let (head, args) = expr::unfold_apps(&normalized);
        let ExprData::Const(name, levels) = &**head else {
            return Ok(None);
        };
        let shift_by = ctx
            .len()
            .checked_sub(current_num_params as usize)
            .ok_or_else(|| TcError::Other("recursive target context underflow".into()))?
            as i32;
        for (member_pos, member) in members.iter().enumerate() {
            if *name != member.source_name
                || levels.len() != member.source_levels.len()
                || !levels
                    .iter()
                    .zip(member.source_levels.iter())
                    .all(|(a, b)| level::is_def_eq(a, b))
                || args.len() != member.fixed_params.len() + member.num_indices as usize
            {
                continue;
            }
            let mut params_match = true;
            for (actual, fixed) in args.iter().zip(member.fixed_params.iter()) {
                let expected = expr::shift(fixed, shift_by, 0);
                if !self.is_def_eq(ctx, actual, &expected)? {
                    params_match = false;
                    break;
                }
            }
            if params_match {
                return Ok(Some((
                    member_pos,
                    args[member.fixed_params.len()..].to_vec(),
                )));
            }
        }
        Ok(None)
    }

    fn contains_current_member(
        &self,
        e: &Expr,
        local_depth: u32,
        current_num_params: u32,
        original_names: &[u32],
        members: &[RecMember],
    ) -> bool {
        if let ExprData::Const(n, _) = &***e {
            if original_names.contains(n) {
                return true;
            }
        }
        if members.iter().any(|member| {
            self.member_prefix_matches_at_depth(
                member,
                e,
                current_num_params,
                current_num_params as usize + local_depth as usize,
            )
            .is_some()
        })
        {
            return true;
        }
        match &***e {
            ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {
                false
            }
            ExprData::App(f, a) => {
                self.contains_current_member(
                    f,
                    local_depth,
                    current_num_params,
                    original_names,
                    members,
                ) || self.contains_current_member(
                    a,
                    local_depth,
                    current_num_params,
                    original_names,
                    members,
                )
            }
            ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
                self.contains_current_member(
                    ty,
                    local_depth,
                    current_num_params,
                    original_names,
                    members,
                ) || self.contains_current_member(
                    body,
                    local_depth + 1,
                    current_num_params,
                    original_names,
                    members,
                )
            }
            ExprData::Let(ty, val, body) => {
                self.contains_current_member(
                    ty,
                    local_depth,
                    current_num_params,
                    original_names,
                    members,
                ) || self.contains_current_member(
                    val,
                    local_depth,
                    current_num_params,
                    original_names,
                    members,
                ) || self.contains_current_member(
                    body,
                    local_depth + 1,
                    current_num_params,
                    original_names,
                    members,
                )
            }
            ExprData::Proj(_, _, v) => self.contains_current_member(
                v,
                local_depth,
                current_num_params,
                original_names,
                members,
            ),
        }
    }

    fn nested_occurrence(
        &self,
        e: &Expr,
        local_depth: u32,
        current_num_params: u32,
        original_names: &[u32],
        members: &[RecMember],
    ) -> R<Option<NestedOccurrence>> {
        if !matches!(&***e, ExprData::App(_, _)) {
            return Ok(None);
        }
        let (head, args) = expr::unfold_apps(e);
        let ExprData::Const(source_name, source_levels) = &**head else {
            return Ok(None);
        };
        // The official transform consults the prior environment.  Current
        // block names are already staged in Kiota's environment, so exclude
        // them explicitly to recover the same boundary.
        if original_names.contains(source_name) {
            return Ok(None);
        }
        let (source_all, source_num_params) = match self.env.get(*source_name) {
            Some(ConstantInfo::InductiveType {
                all, num_params, ..
            }) => (all.clone(), *num_params),
            _ => return Ok(None),
        };
        if args.len() < source_num_params as usize {
            return Ok(None);
        }
        let source_params = &args[..source_num_params as usize];
        if !source_params.iter().any(|p| {
            self.contains_current_member(
                p,
                local_depth,
                current_num_params,
                original_names,
                members,
            )
        }) {
            return Ok(None);
        }
        if source_params
            .iter()
            .any(|p| has_bvar_in_range(p, 0, local_depth, 0))
        {
            return reject(format!(
                "invalid nested inductive datatype `{}`: parameters contain constructor-local variables",
                self.name_str(*source_name)
            ));
        }
        let fixed_params = source_params
            .iter()
            .map(|p| expr::shift(p, -(local_depth as i32), 0))
            .collect();
        Ok(Some(NestedOccurrence {
            source_name: *source_name,
            source_levels: source_levels.as_ref().clone(),
            fixed_params,
            source_all,
            source_num_params,
        }))
    }

    fn add_nested_specialization(
        &self,
        occurrence: NestedOccurrence,
        current_params: &[RecBinder],
        members: &mut Vec<RecMember>,
    ) -> R<()> {
        if members.iter().any(|member| {
            member.source_name == occurrence.source_name
                && member.source_levels == occurrence.source_levels
                && rec_exprs_eq(&member.fixed_params, &occurrence.fixed_params)
        }) {
            return Ok(());
        }
        for source_member in &occurrence.source_all {
            let (level_params, typ, num_params, num_indices, ctor_names) =
                match self.env.get(*source_member) {
                    Some(ConstantInfo::InductiveType {
                        level_params,
                        typ,
                        num_params,
                        num_indices,
                        ctors,
                        all,
                        ..
                    }) if all == &occurrence.source_all => (
                        level_params.clone(),
                        typ.clone(),
                        *num_params,
                        *num_indices,
                        ctors.clone(),
                    ),
                    _ => return reject("invalid prior mutual group during nested reconstruction"),
                };
            if num_params != occurrence.source_num_params {
                return reject("inconsistent parameter count in prior nested mutual group");
            }
            let specialized_typ = self.specialize_prior_telescope(
                &typ,
                &level_params,
                &occurrence.source_levels,
                num_params,
                &occurrence.fixed_params,
                current_params,
            )?;
            let mut ctors = Vec::with_capacity(ctor_names.len());
            for cname in ctor_names {
                let (ctor_level_params, ctor_typ, ctor_num_params) = match self.env.get(cname) {
                    Some(ConstantInfo::Constructor {
                        level_params,
                        typ,
                        num_params,
                        ..
                    }) => (level_params.clone(), typ.clone(), *num_params),
                    _ => return reject("missing prior constructor during nested reconstruction"),
                };
                if ctor_num_params != num_params {
                    return reject("prior nested constructor has inconsistent parameters");
                }
                let specialized_ctor = self.specialize_prior_telescope(
                    &ctor_typ,
                    &ctor_level_params,
                    &occurrence.source_levels,
                    num_params,
                    &occurrence.fixed_params,
                    current_params,
                )?;
                ctors.push(RecConstructor {
                    name: cname,
                    levels: occurrence.source_levels.clone(),
                    typ: specialized_ctor,
                });
            }
            members.push(RecMember {
                source_name: *source_member,
                source_levels: occurrence.source_levels.clone(),
                fixed_params: occurrence.fixed_params.clone(),
                typ: specialized_typ,
                num_indices,
                ctors,
            });
        }
        Ok(())
    }

    fn scan_nested_expr(
        &self,
        e: &Expr,
        local_depth: u32,
        current_num_params: u32,
        current_params: &[RecBinder],
        original_names: &[u32],
        members: &mut Vec<RecMember>,
    ) -> R<()> {
        if let Some(occurrence) = self.nested_occurrence(
            e,
            local_depth,
            current_num_params,
            original_names,
            members,
        )? {
            // `replace` in Lean's transform is outermost-first.  Once this
            // application becomes an auxiliary target it does not descend
            // into its parameters; copied constructors expose deeper
            // specializations to later BFS worklist entries instead.
            return self.add_nested_specialization(occurrence, current_params, members);
        }
        match &***e {
            ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {
                Ok(())
            }
            ExprData::App(f, a) => {
                self.scan_nested_expr(
                    f,
                    local_depth,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )?;
                self.scan_nested_expr(
                    a,
                    local_depth,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )
            }
            ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
                self.scan_nested_expr(
                    ty,
                    local_depth,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )?;
                self.scan_nested_expr(
                    body,
                    local_depth + 1,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )
            }
            ExprData::Let(ty, val, body) => {
                self.scan_nested_expr(
                    ty,
                    local_depth,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )?;
                self.scan_nested_expr(
                    val,
                    local_depth,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )?;
                self.scan_nested_expr(
                    body,
                    local_depth + 1,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )
            }
            ExprData::Proj(_, _, v) => self.scan_nested_expr(
                v,
                local_depth,
                current_num_params,
                current_params,
                original_names,
                members,
            ),
        }
    }

    fn expand_nested_members(
        &self,
        original_names: &[u32],
        current_num_params: u32,
        current_params: &[RecBinder],
        members: &mut Vec<RecMember>,
    ) -> R<()> {
        let mut qhead = 0usize;
        while qhead < members.len() {
            let ctors = members[qhead].ctors.clone();
            for ctor in ctors {
                let mut ctx = Ctx::new();
                let mut cur = ctor.typ;
                for _ in 0..current_num_params {
                    let (_, dom, body) = self.ensure_pi(&ctx, &cur)?;
                    ctx.push(dom);
                    cur = body;
                }
                self.scan_nested_expr(
                    &cur,
                    0,
                    current_num_params,
                    current_params,
                    original_names,
                    members,
                )?;
            }
            qhead += 1;
        }
        Ok(())
    }

    fn expanded_prop_only(
        &self,
        original_names: &[u32],
        members: &[RecMember],
        num_params: u32,
    ) -> R<bool> {
        let mut result_level: Option<Level> = None;
        for member in members {
            let mut ctx = Ctx::new();
            let mut cur = member.typ.clone();
            for _ in 0..(num_params + member.num_indices) {
                let (_, dom, body) = self.ensure_pi(&ctx, &cur)?;
                ctx.push(dom);
                cur = body;
            }
            let member_level = self.ensure_sort(&ctx, &cur)?;
            if let Some(first_level) = &result_level {
                if !level::is_def_eq(first_level, &member_level) {
                    return reject(
                        "nested auxiliary member has a different result universe",
                    );
                }
            } else {
                result_level = Some(member_level);
            }
        }
        if members.len() == original_names.len() {
            return self.elim_only_at_universe_zero(original_names);
        }
        let result_level = result_level
            .ok_or_else(|| TcError::Other("expanded recursor group is empty".into()))?;
        // The transformed declaration is mutual as soon as it has one copied
        // member, so Lean restricts every possibly-Prop result to Prop.
        Ok(!level::is_not_zero(&result_level))
    }

    /// Reconstruct ordinary, mutual and nested recursor types from checked
    /// types and constructors.  Nested members are discovered by the same
    /// breadth-first transformation order as Lean, but are represented in
    /// restored form throughout: no auxiliary name or supplied recursor is
    /// ever made visible in the environment.
    pub(crate) fn reconstruct_recursors(
        &self,
        type_names: &[u32],
        supplied_level_params: &[u32],
    ) -> R<Vec<DerivedRecursor>> {
        let Some(&first) = type_names.first() else {
            return reject("cannot reconstruct recursors for an empty inductive group");
        };
        let (all, num_params, shared_lparams, first_typ) = match self.env.get(first) {
            Some(ConstantInfo::InductiveType {
                all,
                num_params,
                level_params,
                typ,
                ..
            }) => (all.clone(), *num_params, level_params.clone(), typ.clone()),
            _ => return reject("recursor reconstruction requires an inductive type"),
        };
        if all.as_slice() != type_names {
            return reject("recursor reconstruction group is not the inductive declaration order");
        }
        for t in &all {
            match self.env.get(*t) {
                Some(ConstantInfo::InductiveType {
                    all: a,
                    num_params: p,
                    level_params,
                    ..
                }) if a == &all && *p == num_params && level_params == &shared_lparams => {}
                _ => {
                    return reject(
                        "inconsistent mutual inductive group during recursor reconstruction",
                    )
                }
            }
        }

        // Discovery precedes the elimination-level decision because adding a
        // nested member changes Lean's Prop-elimination rule.  Use the checked
        // declaration level names for this shape-only pass.
        let discovery_levels: Vec<Level> =
            shared_lparams.iter().copied().map(level::param).collect();
        let discovery_subst = level::subst_map(&shared_lparams, &discovery_levels);
        let discovery_params = self.rec_params(&first_typ, num_params, &discovery_subst)?;
        let mut discovery_members = self.original_rec_members(
            &all,
            num_params,
            &discovery_subst,
            &discovery_levels,
        )?;
        self.expand_nested_members(
            &all,
            num_params,
            &discovery_params,
            &mut discovery_members,
        )?;
        let prop_only =
            self.expanded_prop_only(&all, &discovery_members, num_params)?;

        if !ids_are_pairwise_distinct(supplied_level_params) {
            return reject("recursor has duplicate universe parameters");
        }
        let level_params = if prop_only {
            if supplied_level_params.len() != shared_lparams.len() {
                return reject("Prop-only recursor has the wrong universe-parameter shape");
            }
            supplied_level_params.to_vec()
        } else {
            if supplied_level_params.len() != shared_lparams.len() + 1 {
                return reject("recursor is missing its fresh elimination universe parameter");
            }
            // Pairwise distinctness above establishes freshness against the
            // supplied declaration tail, which is the alpha-renamed tail
            // actually used to construct this recursor.
            supplied_level_params.to_vec()
        };
        let elim_level = if prop_only {
            level::zero()
        } else {
            level::param(level_params[0])
        };
        let decl_levels: Vec<Level> = if prop_only {
            level_params.iter().copied().map(level::param).collect()
        } else {
            level_params[1..].iter().copied().map(level::param).collect()
        };
        let level_subst = level::subst_map(&shared_lparams, &decl_levels);
        let params = self.rec_params(&first_typ, num_params, &level_subst)?;
        let mut members = self.original_rec_members(
            &all,
            num_params,
            &level_subst,
            &decl_levels,
        )?;
        self.expand_nested_members(&all, num_params, &params, &mut members)?;
        if members.len() != discovery_members.len() {
            return Err(TcError::Other(
                "nested recursor discovery changed under universe alpha-renaming".into(),
            ));
        }

        let num_minors: u32 = members.iter().map(|m| m.ctors.len() as u32).sum();
        let k = members.len() == 1 && self.is_k_like(&all)?;
        let mut out = Vec::with_capacity(members.len());
        for target_pos in 0..members.len() {
            let typ = self.build_base_recursor_type(
                &all,
                &members,
                target_pos,
                num_params,
                &params,
                elim_level.clone(),
            )?;
            out.push(DerivedRecursor {
                typ,
                level_params: level_params.clone(),
                // Lean restores every recursor's metadata to the original
                // declared group, even auxiliary `.rec_N` recursors.
                all: all.clone(),
                num_params,
                num_indices: members[target_pos].num_indices,
                num_motives: members.len() as u32,
                num_minors,
                k,
            });
        }
        Ok(out)
    }

    /// Infer both closed types after positional universe-alpha normalization,
    /// then compare them in the empty context.  Collision-free canonical
    /// parameters keep undeclared parameters (which inference must itself
    /// reject or preserve) from being accidentally captured by normalization.
    pub(crate) fn validate_reconstructed_type(
        &self,
        supplied: &Expr,
        supplied_level_params: &[u32],
        reconstructed: &Expr,
        reconstructed_level_params: &[u32],
    ) -> R<()> {
        if !expr::is_closed(supplied) || !expr::is_closed(reconstructed) {
            return reject("recursor type is not closed");
        }
        if supplied_level_params.len() != reconstructed_level_params.len()
            || !ids_are_pairwise_distinct(supplied_level_params)
            || !ids_are_pairwise_distinct(reconstructed_level_params)
        {
            return reject("recursor universe parameters do not match positionally");
        }
        let mut supplied_used = Vec::new();
        collect_level_ids_expr(supplied, &mut supplied_used);
        if supplied_used
            .iter()
            .any(|id| !supplied_level_params.contains(id))
        {
            return reject("recursor type uses an undeclared universe parameter");
        }
        let mut reconstructed_used = Vec::new();
        collect_level_ids_expr(reconstructed, &mut reconstructed_used);
        if reconstructed_used
            .iter()
            .any(|id| !reconstructed_level_params.contains(id))
        {
            return Err(TcError::Other(
                "reconstructed recursor uses an undeclared universe parameter".into(),
            ));
        }
        let mut used = supplied_level_params.to_vec();
        for id in reconstructed_level_params {
            if !used.contains(id) {
                used.push(*id);
            }
        }
        for id in supplied_used.into_iter().chain(reconstructed_used) {
            if !used.contains(&id) {
                used.push(id);
            }
        }
        let mut next = u32::MAX;
        let mut canonical = Vec::with_capacity(supplied_level_params.len());
        for _ in supplied_level_params {
            while used.contains(&next) {
                next = next
                    .checked_sub(1)
                    .ok_or_else(|| TcError::Other("cannot allocate canonical universe parameter".into()))?;
            }
            canonical.push(level::param(next));
            used.push(next);
            next = next
                .checked_sub(1)
                .ok_or_else(|| TcError::Other("cannot allocate canonical universe parameter".into()))?;
        }
        let supplied_subst = level::subst_map(supplied_level_params, &canonical);
        let reconstructed_subst =
            level::subst_map(reconstructed_level_params, &canonical);
        let supplied = expr::instantiate_level_params(supplied, &supplied_subst);
        let reconstructed =
            expr::instantiate_level_params(reconstructed, &reconstructed_subst);
        let ctx = Ctx::new();
        self.ensure_sort(&ctx, &self.infer_type(&ctx, &supplied)?)?;
        self.ensure_sort(&ctx, &self.infer_type(&ctx, &reconstructed)?)?;
        if self.is_def_eq(&ctx, &supplied, &reconstructed)? {
            Ok(())
        } else {
            reject("recursor type does not match reconstructed type")
        }
    }

    fn member_app(
        &self,
        member: &RecMember,
        num_params: u32,
        total_depth: usize,
        indices: &[Expr],
    ) -> R<Expr> {
        let shift_by = total_depth
            .checked_sub(num_params as usize)
            .ok_or_else(|| TcError::Other("recursor member context underflow".into()))?
            as i32;
        let mut args: Vec<Expr> = member
            .fixed_params
            .iter()
            .map(|p| expr::shift(p, shift_by, 0))
            .collect();
        args.extend(indices.iter().cloned());
        Ok(expr::apps(
            expr::const_(member.source_name, member.source_levels.clone()),
            &args,
        ))
    }

    fn build_base_recursor_type(
        &self,
        original_names: &[u32],
        members: &[RecMember],
        target_pos: usize,
        num_params: u32,
        params: &[RecBinder],
        elim_level: Level,
    ) -> R<Expr> {
        let mut binders = params.to_vec();

        for member in members {
            let motive_base = binders.len();
            let mut src_ctx = Ctx::new();
            let mut cur = member.typ.clone();
            for _ in 0..num_params {
                let (_, dom, body) = self.ensure_pi(&src_ctx, &cur)?;
                src_ctx.push(dom);
                cur = body;
            }
            let mut indices = Vec::with_capacity(member.num_indices as usize);
            for index_pos in 0..member.num_indices as usize {
                let (bi, dom, body) = self.ensure_pi(&src_ctx, &cur)?;
                let shift_by = motive_base
                    .checked_sub(num_params as usize)
                    .ok_or_else(|| TcError::Other("motive context underflow".into()))?
                    as i32;
                indices.push(RecBinder {
                    info: bi,
                    // Preserve already-open index locals; only the outer
                    // shared-parameter context moves past earlier motives.
                    typ: expr::shift(&dom, shift_by, index_pos as u32),
                });
                src_ctx.push(dom);
                cur = body;
            }
            let depth = motive_base + indices.len();
            let index_args: Vec<Expr> = (0..indices.len())
                .map(|i| expr::bvar((indices.len() - 1 - i) as u32))
                .collect();
            let major = self.member_app(member, num_params, depth, &index_args)?;
            let result = expr::pi(
                BinderInfo::Default,
                major,
                expr::sort(elim_level.clone()),
            );
            binders.push(RecBinder {
                info: BinderInfo::Default,
                typ: close_rec_telescope(&indices, result),
            });
        }

        for (owner_pos, owner) in members.iter().enumerate() {
            for ctor in &owner.ctors {
                let minor = self.build_minor_type(
                    original_names,
                    members,
                    owner_pos,
                    ctor,
                    num_params,
                    binders.len(),
                )?;
                binders.push(RecBinder {
                    info: BinderInfo::Default,
                    typ: minor,
                });
            }
        }

        let target = &members[target_pos];
        let mut src_ctx = Ctx::new();
        let mut cur = target.typ.clone();
        for _ in 0..num_params {
            let (_, dom, body) = self.ensure_pi(&src_ctx, &cur)?;
            src_ctx.push(dom);
            cur = body;
        }
        let indices_base = binders.len();
        for index_pos in 0..target.num_indices as usize {
            let (bi, dom, body) = self.ensure_pi(&src_ctx, &cur)?;
            let shift_by = indices_base
                .checked_sub(num_params as usize)
                .ok_or_else(|| TcError::Other("target-index context underflow".into()))?
                as i32;
            binders.push(RecBinder {
                info: bi,
                typ: expr::shift(&dom, shift_by, index_pos as u32),
            });
            src_ctx.push(dom);
            cur = body;
        }
        let before_major = binders.len();
        let index_args: Vec<Expr> = (0..target.num_indices as usize)
            .map(|i| expr::bvar((target.num_indices as usize - 1 - i) as u32))
            .collect();
        let major_ty = self.member_app(target, num_params, before_major, &index_args)?;
        binders.push(RecBinder {
            info: BinderInfo::Default,
            typ: major_ty,
        });

        let depth = binders.len();
        let motive_pos = num_params as usize + target_pos;
        let motive = expr::bvar((depth - 1 - motive_pos) as u32);
        let mut result_args: Vec<Expr> = (0..target.num_indices as usize)
            .map(|i| expr::bvar(target.num_indices - i as u32))
            .collect();
        result_args.push(expr::bvar(0));
        Ok(close_rec_telescope(
            &binders,
            expr::apps(motive, &result_args),
        ))
    }

    fn build_minor_type(
        &self,
        original_names: &[u32],
        members: &[RecMember],
        owner_pos: usize,
        ctor: &RecConstructor,
        num_params: u32,
        outer_depth: usize,
    ) -> R<Expr> {
        let mut src_ctx = Ctx::new();
        let mut cur = ctor.typ.clone();
        for _ in 0..num_params {
            let (_, dom, body) = self.ensure_pi(&src_ctx, &cur)?;
            src_ctx.push(dom);
            cur = body;
        }
        struct Field {
            info: BinderInfo,
            dom: Expr,
            ctx: Ctx,
        }
        let mut fields = Vec::new();
        loop {
            match self.ensure_pi(&src_ctx, &cur) {
                Ok((bi, dom, body)) => {
                    fields.push(Field {
                        info: bi,
                        dom: dom.clone(),
                        ctx: src_ctx.clone(),
                    });
                    src_ctx.push(dom);
                    cur = body;
                }
                Err(_) => break,
            }
        }
        let field_count = fields.len();
        let mut local = Vec::with_capacity(field_count);
        let field_shift = outer_depth
            .checked_sub(num_params as usize)
            .ok_or_else(|| TcError::Other("minor context underflow".into()))?
            as i32;
        for (field_pos, field) in fields.iter().enumerate() {
            local.push(RecBinder {
                info: field.info,
                // Earlier constructor fields stay local; only the parameter
                // prefix moves across motives and preceding minors.
                typ: expr::shift(&field.dom, field_shift, field_pos as u32),
            });
        }

        let Some((conclusion_owner, conclusion_indices)) = self.find_member_target(
            members,
            &cur,
            num_params,
            num_params as usize + field_count,
        ) else {
            return reject("constructor conclusion is outside reconstructed mutual group");
        };
        if conclusion_owner != owner_pos {
            return reject("constructor conclusion has the wrong reconstructed owner");
        }

        let mut ih_count = 0usize;
        for (field_pos, field) in fields.iter().enumerate() {
            let mut fctx = field.ctx.clone();
            let mut fcur = self.whnf(&fctx, &field.dom)?;
            let mut arg_binders = Vec::new();
            loop {
                match self.ensure_pi(&fctx, &fcur) {
                    Ok((bi, dom, body)) => {
                        let outer_shift = outer_depth
                            .checked_sub(num_params as usize)
                            .ok_or_else(|| {
                                TcError::Other("recursive-field outer context underflow".into())
                            })? as i32;
                        let arg_depth = arg_binders.len();
                        let with_outer = expr::shift(
                            &dom,
                            outer_shift,
                            (arg_depth + field_pos) as u32,
                        );
                        let inner_shift = field_count - field_pos + ih_count;
                        arg_binders.push(RecBinder {
                            info: bi,
                            // Source: params, prior fields, prior function args.
                            // Destination: params, motives/minors, all fields,
                            // prior IHs, prior function args.  Motives/minors
                            // are inserted outside the prior fields, whereas
                            // the current/later fields and prior IHs are
                            // inserted inside them, so this cannot be one
                            // uniform shift.
                            typ: expr::shift(&with_outer, inner_shift as i32, arg_depth as u32),
                        });
                        fctx.push(dom);
                        fcur = body;
                    }
                    Err(_) => break,
                }
            }
            let recursive_target = if let Some(found) = self.find_member_target(
                members,
                &fcur,
                num_params,
                fctx.len(),
            ) {
                Some(found)
            } else {
                self.find_member_target_defeq(members, &fcur, num_params, &fctx)?
            };
            let Some((member_pos, recursive_indices)) = recursive_target else {
                let local_depth = fctx
                    .len()
                    .checked_sub(num_params as usize)
                    .ok_or_else(|| {
                        TcError::Other("recursive-field source context underflow".into())
                    })? as u32;
                if self.contains_current_member(
                    &fcur,
                    local_depth,
                    num_params,
                    original_names,
                    members,
                ) {
                    return reject(
                        "recursive field does not exactly match a reconstructed member specialization",
                    );
                }
                continue;
            };
            let base = outer_depth + field_count + ih_count;
            let outer_shift = outer_depth
                .checked_sub(num_params as usize)
                .ok_or_else(|| TcError::Other("recursive target outer context underflow".into()))?
                as i32;
            let inner_shift = field_count - field_pos + ih_count;
            let arg_count = arg_binders.len();
            let depth = base + arg_count;
            let motive_pos = num_params as usize + member_pos;
            let motive = expr::bvar((depth - 1 - motive_pos) as u32);
            let mut ih_args: Vec<Expr> = recursive_indices
                .iter()
                .map(|a| {
                    let with_outer = expr::shift(
                        a,
                        outer_shift,
                        (arg_count + field_pos) as u32,
                    );
                    expr::shift(&with_outer, inner_shift as i32, arg_count as u32)
                })
                .collect();
            let field_value = expr::bvar(
                (field_count + ih_count + arg_count - 1 - field_pos) as u32,
            );
            let function_args: Vec<Expr> = (0..arg_count)
                .map(|i| expr::bvar((arg_count - 1 - i) as u32))
                .collect();
            ih_args.push(expr::apps(field_value, &function_args));
            local.push(RecBinder {
                info: BinderInfo::Default,
                typ: close_rec_telescope(&arg_binders, expr::apps(motive, &ih_args)),
            });
            ih_count += 1;
        }

        let depth = outer_depth + field_count + ih_count;
        let conclusion_outer_shift = outer_depth
            .checked_sub(num_params as usize)
            .ok_or_else(|| TcError::Other("constructor conclusion context underflow".into()))?
            as i32;
        let motive = expr::bvar((depth - 1 - (num_params as usize + owner_pos)) as u32);
        let mut result_args: Vec<Expr> = conclusion_indices
            .iter()
            .map(|a| {
                // First insert motives/minors between parameters and fields;
                // then insert the accumulated IHs above every field.  A
                // single shift with `field_count` cutoff would leave field
                // bvars pointing at those newly inserted IH binders.
                let with_outer = expr::shift(
                    a,
                    conclusion_outer_shift,
                    field_count as u32,
                );
                expr::shift(&with_outer, ih_count as i32, 0)
            })
            .collect();
        let owner = &members[owner_pos];
        let fixed_shift = depth
            .checked_sub(num_params as usize)
            .ok_or_else(|| TcError::Other("constructor application context underflow".into()))?
            as i32;
        let mut ctor_args: Vec<Expr> = owner
            .fixed_params
            .iter()
            .map(|p| expr::shift(p, fixed_shift, 0))
            .collect();
        ctor_args.extend(
            (0..field_count)
                .map(|i| expr::bvar((field_count + ih_count - 1 - i) as u32)),
        );
        result_args.push(expr::apps(
            expr::const_(ctor.name, ctor.levels.clone()),
            &ctor_args,
        ));
        Ok(close_rec_telescope(
            &local,
            expr::apps(motive, &result_args),
        ))
    }

}
