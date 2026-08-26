use crate::env::{ConstantInfo, Environment, QuotKind, RecRule, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr, ExprData};
use crate::level::{self, Level};
use crate::tc::{Checker, TcError};
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::Value;
use std::io::{BufRead, Write};
use std::rc::Rc;

pub struct Parser {
    pub names: Vec<Rc<String>>, // index -> full dotted name (for diagnostics / builtin lookup)
    pub name_by_str: FxHashMap<String, u32>,
    pub levels: Vec<Level>,
    pub exprs: Vec<Expr>,
    pub env: Environment,
    pub decl_count: usize,
}

fn bi_of(s: &str) -> BinderInfo {
    match s {
        "implicit" => BinderInfo::Implicit,
        "strictImplicit" => BinderInfo::StrictImplicit,
        "instImplicit" => BinderInfo::InstImplicit,
        _ => BinderInfo::Default,
    }
}

impl Parser {
    pub fn new() -> Self {
        if let Ok(n) = std::env::var("KIOTA_WARM_INTERN") {
            if let Ok(n) = n.parse::<u32>() {
                crate::expr::warm_intern(n);
                eprintln!("WARM_INTERN {n} nodes={}", crate::expr::intern_node_count());
            }
        }
        Parser {
            names: vec![Rc::new(String::new())], // index 0 = anonymous
            name_by_str: FxHashMap::default(),
            levels: vec![level::zero()], // index 0 = zero
            exprs: Vec::new(),
            env: Environment::default(),
            decl_count: 0,
        }
    }

    fn get_u32(v: &Value, k: &str) -> u32 {
        v.get(k).and_then(|x| x.as_u64()).unwrap_or(0) as u32
    }

    fn require_u32(v: &Value, k: &str) -> Result<u32, TcError> {
        match v.get(k) {
            None => Err(TcError::Reject(format!("missing required field `{k}`"))),
            Some(x) => match x.as_u64() {
                Some(n) if n <= u32::MAX as u64 => Ok(n as u32),
                _ => Err(TcError::Reject(format!("field `{k}` must be a u32"))),
            },
        }
    }

    fn require_expr(&self, v: &Value, k: &str) -> Result<Expr, TcError> {
        let i = Self::require_u32(v, k)?;
        self.exprs
            .get(i as usize)
            .cloned()
            .ok_or_else(|| TcError::Reject(format!("expr index {i} for `{k}` is out of range")))
    }

    fn get_str<'a>(v: &'a Value, k: &str) -> &'a str {
        v.get(k).and_then(|x| x.as_str()).unwrap_or("")
    }
    fn get_bool(v: &Value, k: &str) -> bool {
        v.get(k).and_then(|x| x.as_bool()).unwrap_or(false)
    }
    fn require_bool(v: &Value, k: &str) -> Result<bool, TcError> {
        match v.get(k) {
            None => Err(TcError::Reject(format!("missing required field `{k}`"))),
            Some(x) => x
                .as_bool()
                .ok_or_else(|| TcError::Reject(format!("field `{k}` must be a bool"))),
        }
    }
    fn get_vec_u32(v: &Value, k: &str) -> Vec<u32> {
        v.get(k)
            .and_then(|x| x.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|e| e.as_u64())
                    .map(|n| n as u32)
                    .collect()
            })
            .unwrap_or_default()
    }

    fn pair_u32(v: &Value) -> (u32, u32) {
        if let Some(arr) = v.as_array() {
            let a = arr.get(0).and_then(|x| x.as_u64()).unwrap_or(0) as u32;
            let b = arr.get(1).and_then(|x| x.as_u64()).unwrap_or(0) as u32;
            (a, b)
        } else {
            (Self::get_u32(v, "lhs"), Self::get_u32(v, "rhs"))
        }
    }

    fn level_at(&self, i: u32) -> Level {
        self.levels[i as usize].clone()
    }
    fn expr_at(&self, i: u32) -> Expr {
        self.exprs[i as usize].clone()
    }

    fn handle_name(&mut self, idx: u32, v: &Value) {
        let full = if let Some(s) = v.get("str") {
            let pre = Self::get_u32(s, "pre");
            let seg = Self::get_str(s, "str");
            let parent = &*self.names[pre as usize];
            if parent.is_empty() {
                seg.to_string()
            } else {
                format!("{}.{}", parent, seg)
            }
        } else if let Some(n) = v.get("num") {
            let pre = Self::get_u32(n, "pre");
            let i = n.get("i").and_then(|x| x.as_u64()).unwrap_or(0);
            let parent = &*self.names[pre as usize];
            if parent.is_empty() {
                format!("{}", i)
            } else {
                format!("{}.{}", parent, i)
            }
        } else {
            String::new()
        };
        while self.names.len() <= idx as usize {
            self.names.push(Rc::new(String::new()));
        }
        self.name_by_str.insert(full.clone(), idx);
        self.names[idx as usize] = Rc::new(full);
    }

    fn handle_level(&mut self, idx: u32, v: &Value) {
        let l = if let Some(a) = v.get("succ") {
            level::succ(self.level_at(a.as_u64().unwrap() as u32))
        } else if let Some(m) = v.get("max") {
            let (a, b) = Self::pair_u32(m);
            level::max(self.level_at(a), self.level_at(b))
        } else if let Some(m) = v.get("imax") {
            let (a, b) = Self::pair_u32(m);
            level::imax(self.level_at(a), self.level_at(b))
        } else if let Some(p) = v.get("param") {
            level::param(p.as_u64().unwrap() as u32)
        } else {
            level::zero()
        };
        while self.levels.len() <= idx as usize {
            self.levels.push(level::zero());
        }
        self.levels[idx as usize] = l;
    }

    fn handle_expr(&mut self, idx: u32, v: &Value) -> Result<(), TcError> {
        let e = if let Some(l) = v.get("sort") {
            expr::sort(self.level_at(l.as_u64().unwrap() as u32))
        } else if let Some(c) = v.get("const") {
            let name = Self::get_u32(c, "name");
            let us = Self::get_vec_u32(c, "us")
                .into_iter()
                .map(|i| self.level_at(i))
                .collect();
            expr::const_(name, us)
        } else if let Some(b) = v.get("bvar") {
            expr::bvar(b.as_u64().unwrap() as u32)
        } else if let Some(a) = v.get("app") {
            let f = self.expr_at(Self::get_u32(a, "fn"));
            let x = self.expr_at(Self::get_u32(a, "arg"));
            expr::app(f, x)
        } else if let Some(l) = v.get("lam") {
            let bi = bi_of(Self::get_str(l, "binderInfo"));
            let ty = self.expr_at(Self::get_u32(l, "type"));
            let body = self.expr_at(Self::get_u32(l, "body"));
            expr::lam(bi, ty, body)
        } else if let Some(p) = v.get("forallE") {
            let bi = bi_of(Self::get_str(p, "binderInfo"));
            let ty = self.expr_at(Self::get_u32(p, "type"));
            let body = self.expr_at(Self::get_u32(p, "body"));
            expr::pi(bi, ty, body)
        } else if let Some(l) = v.get("letE") {
            let ty = self.expr_at(Self::get_u32(l, "type"));
            let val = self.expr_at(Self::get_u32(l, "value"));
            let body = self.expr_at(Self::get_u32(l, "body"));
            expr::let_(ty, val, body)
        } else if let Some(p) = v.get("proj") {
            let s = Self::get_u32(p, "typeName");
            let i = Self::get_u32(p, "idx");
            let e2 = self.expr_at(Self::get_u32(p, "struct"));
            expr::proj(s, i, e2)
        } else if let Some(n) = v.get("natVal") {
            let s = n.as_str().unwrap_or("0");
            let n: BigUint = s.parse().unwrap_or_default();
            expr::lit_nat(n)
        } else if let Some(s) = v.get("strVal") {
            let s = s.as_str().unwrap_or("").to_string();
            expr::lit_str(s)
        } else if let Some(m) = v.get("mdata") {
            // Metadata wraps an expr; ignore metadata, use inner expr.
            self.expr_at(Self::get_u32(m, "expr"))
        } else {
            return Err(TcError::Reject("unknown expr kind".into()));
        };
        while self.exprs.len() <= idx as usize {
            self.exprs.push(expr::sort(level::zero()));
        }
        self.exprs[idx as usize] = e;
        Ok(())
    }

    fn require_hints(v: &Value) -> Result<ReducibilityHints, TcError> {
        match v.get("hints") {
            None => Err(TcError::Reject("missing required field `hints`".into())),
            Some(Value::String(s)) => match s.as_str() {
                "opaque" => Ok(ReducibilityHints::Opaque),
                "abbrev" => Ok(ReducibilityHints::Abbrev),
                other => Err(TcError::Reject(format!("unknown hints `{other}`"))),
            },
            Some(Value::Object(o)) => match o.get("regular").and_then(|x| x.as_u64()) {
                Some(n) if n <= u32::MAX as u64 => Ok(ReducibilityHints::Regular(n as u32)),
                _ => Err(TcError::Reject(
                    "hints object must have a u32 `regular` field".into(),
                )),
            },
            _ => Err(TcError::Reject("invalid hints".into())),
        }
    }

    fn name_str(&self, n: u32) -> &str {
        self.names.get(n as usize).map(|s| s.as_str()).unwrap_or("")
    }

    fn reject_if_dup(&self, name: u32) -> Result<(), TcError> {
        if self.env.get(name).is_some() {
            return Err(TcError::Reject(format!(
                "duplicate declaration of {}",
                self.names
                    .get(name as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?")
            )));
        }
        Ok(())
    }

    fn handle_def_like(&mut self, kind: &str, v: &Value) -> Result<(), TcError> {
        let name = Self::require_u32(v, "name")?;
        self.reject_if_dup(name)?;
        let level_params = Self::get_vec_u32(v, "levelParams");
        let typ = self.require_expr(v, "type")?;
        match kind {
            "axiomDecl" | "axiom" => {
                let is_unsafe = Self::get_bool(v, "isUnsafe");
                if is_unsafe {
                    return Err(TcError::Reject("unsafe axiom".into()));
                }
                self.env.insert(
                    name,
                    ConstantInfo::Axiom {
                        level_params,
                        typ,
                        is_unsafe,
                    },
                );
            }
            "defnDecl" | "def" => {
                let value = self.require_expr(v, "value")?;
                let hints = Self::require_hints(v)?;
                let safety = Self::get_str(v, "safety");
                if safety == "unsafe" || safety == "partial" {
                    return Err(TcError::Reject(format!("{safety} definition")));
                }
                let is_unsafe = false;
                self.env.insert(
                    name,
                    ConstantInfo::Def {
                        level_params,
                        typ,
                        value,
                        hints,
                        is_unsafe,
                    },
                );
            }
            "thmDecl" | "theorem" => {
                let value = self.require_expr(v, "value")?;
                self.env.insert(
                    name,
                    ConstantInfo::Theorem {
                        level_params,
                        typ,
                        value,
                    },
                );
            }
            "opaqueDecl" | "opaque" => {
                let value = self.require_expr(v, "value")?;
                let safety = Self::get_str(v, "safety");
                if safety == "unsafe" || safety == "partial" {
                    return Err(TcError::Reject(format!("{safety} opaque")));
                }
                let is_unsafe = false;
                self.env.insert(
                    name,
                    ConstantInfo::Opaque {
                        level_params,
                        typ,
                        value,
                        is_unsafe,
                    },
                );
            }
            _ => {}
        }
        Ok(())
    }

    fn handle_quot(&mut self, v: &Value) -> Result<(), TcError> {
        let kind_s = v
            .get("kind")
            .and_then(|x| x.as_str())
            .ok_or_else(|| TcError::Reject("quot missing kind".into()))?;
        let kind = match kind_s {
            "type" => QuotKind::Type,
            "ctor" => QuotKind::Ctor,
            "lift" => QuotKind::Lift,
            "ind" => QuotKind::Ind,
            other => {
                return Err(TcError::Reject(format!(
                    "quot kind `{other}` is not type/ctor/lift/ind"
                )))
            }
        };
        let name = Self::require_u32(v, "name")?;
        let level_params = Self::get_vec_u32(v, "levelParams");
        let typ = self.require_expr(v, "type")?;
        self.reject_if_dup(name)?;
        if !quot_type_matches_kind(&kind, &typ) {
            return Err(TcError::Reject(
                "quot type does not match kernel quotient shape".into(),
            ));
        }
        self.env.insert(
            name,
            ConstantInfo::Quot {
                kind,
                level_params,
                typ,
            },
        );
        Ok(())
    }

    fn handle_inductive_block(&mut self, v: &Value) -> Result<(), TcError> {
        let types = v
            .get("types")
            .and_then(|x| x.as_array())
            .cloned()
            .unwrap_or_default();
        let ctors = v
            .get("ctors")
            .and_then(|x| x.as_array())
            .cloned()
            .unwrap_or_default();
        let recs = v
            .get("recs")
            .and_then(|x| x.as_array())
            .cloned()
            .unwrap_or_default();

        for t in &types {
            let name = Self::require_u32(t, "name")?;
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(t, "levelParams");
            let typ = self.require_expr(t, "type")?;
            let num_params = Self::require_u32(t, "numParams")?;
            let num_indices = Self::require_u32(t, "numIndices")?;
            let all = Self::get_vec_u32(t, "all");
            let ctor_names = Self::get_vec_u32(t, "ctors");
            let is_rec = Self::require_bool(t, "isRec")?;
            let is_unsafe = Self::get_bool(t, "isUnsafe");
            if is_unsafe {
                return Err(TcError::Reject(format!(
                    "unsafe inductive `{}`",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
            self.env.insert(
                name,
                ConstantInfo::InductiveType {
                    level_params,
                    typ,
                    num_params,
                    num_indices,
                    all,
                    ctors: ctor_names,
                    is_rec,
                    is_unsafe,
                },
            );
        }
        for c in &ctors {
            let name = Self::require_u32(c, "name")?;
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(c, "levelParams");
            let typ = self.require_expr(c, "type")?;
            let induct = Self::require_u32(c, "induct")?;
            let cidx = Self::require_u32(c, "cidx")?;
            let num_params = Self::require_u32(c, "numParams")?;
            let num_fields = Self::require_u32(c, "numFields")?;
            let is_unsafe = Self::get_bool(c, "isUnsafe");
            if is_unsafe {
                return Err(TcError::Reject(format!(
                    "unsafe constructor `{}`",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
            self.env.insert(
                name,
                ConstantInfo::Constructor {
                    level_params,
                    typ,
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                    is_unsafe,
                },
            );
        }
        for r in &recs {
            let name = Self::require_u32(r, "name")?;
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(r, "levelParams");
            let typ = self.require_expr(r, "type")?;
            let all = Self::get_vec_u32(r, "all");
            let num_params = Self::require_u32(r, "numParams")?;
            let num_indices = Self::require_u32(r, "numIndices")?;
            let num_motives = Self::require_u32(r, "numMotives")?;
            let num_minors = Self::require_u32(r, "numMinors")?;
            let k = Self::get_bool(r, "k");
            let is_unsafe = Self::get_bool(r, "isUnsafe");
            if is_unsafe {
                return Err(TcError::Reject(format!(
                    "unsafe recursor `{}`",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
            let expected =
                num_params as u64 + num_indices as u64 + num_motives as u64 + num_minors as u64 + 1;
            let arity = pi_telescope_len(&typ);
            if arity as u64 != expected {
                return Err(TcError::Reject(format!(
                    "recursor `{}` type telescope length {arity} != {expected}",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
            let rules = if let Some(arr) = r.get("rules").and_then(|x| x.as_array()) {
                let mut out = Vec::with_capacity(arr.len());
                for rule in arr {
                    out.push(RecRule {
                        ctor: Self::require_u32(rule, "ctor")?,
                        nfields: Self::require_u32(rule, "nfields")?,
                        rhs: self.require_expr(rule, "rhs")?,
                    });
                }
                out
            } else {
                Vec::new()
            };
            self.env.insert(
                name,
                ConstantInfo::Recursor {
                    level_params,
                    typ,
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k,
                    is_unsafe,
                },
            );
        }

        // Recursor identity is the inductive of this recursor's *rule
        // constructors*, not the pretty name `I.rec` and not `all[0]`.
        // Nested `Syntax.rec`/`rec_1`/`rec_2` all export `all = [Syntax]`;
        // `rec_2`'s rules are `List.nil`/`List.cons`. Mapping every rec to
        // `all[0]` is a duplicate-recursor reject on type 8527; mapping by
        // `I.rec` rejects a well-typed recursor named `elim`. Empty-rules
        // recursors (`False.rec`) claim `all ∩ group`. Nested rec_k have
        // rules for foreign constructors and must not steal `rec_of[I]`.
        // Extra recursor: more recs than `types + nested specializations
        // reconstructed from ctor fields`, or two recs claiming the same
        // group type. Exported `numNested` / `k` / rule RHS are not trusted.
        let type_names: Vec<u32> = types.iter().map(|t| Self::get_u32(t, "name")).collect();
        let nested_n = self.counted_nested(&type_names);
        let nested = nested_n > 0;
        let expected_recs = type_names.len() + nested_n;
        if recs.len() > expected_recs {
            return Err(TcError::Reject(format!(
                "extra recursor in inductive group ({} recs, expected {expected_recs})",
                recs.len()
            )));
        }
        // `I.rec` is the name Lean reserves for `I`'s recursor, and it is the
        // name every user of the recursor is compiled against. An export that
        // supplies `I.not_rec` instead is not offering a constant the kernel
        // would ever have built, so no amount of checking its *type* makes it
        // legitimate — and a checker that regenerates `I.rec` from the
        // inductive would leave `I.not_rec` dangling for its callers. Nested
        // auxiliaries are `I.rec_1`, `I.rec_2`, …; identity below is still
        // rule constructors, this only fixes what the constant may be called.
        for r in &recs {
            let rname = Self::get_u32(r, "name");
            let rstr = self.name_str(rname);
            let named_for_group = type_names.iter().any(|t| {
                let tstr = self.name_str(*t);
                match rstr.strip_prefix(tstr) {
                    Some(".rec") => true,
                    Some(suf) => suf
                        .strip_prefix(".rec_")
                        .is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit())),
                    None => false,
                }
            });
            if !named_for_group {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` is not named `I.rec` for an inductive in this group"
                )));
            }
        }
        let mut seen_rec_for: FxHashSet<u32> = FxHashSet::default();
        for r in &recs {
            let rname = Self::get_u32(r, "name");
            let rstr = self
                .names
                .get(rname as usize)
                .map(|s| s.as_str())
                .unwrap_or("");
            let all = Self::get_vec_u32(r, "all");
            let rules_arr = r.get("rules").and_then(|x| x.as_array());
            let n_rules = rules_arr.map(|a| a.len()).unwrap_or(0);
            let mut claimed: Vec<u32> = Vec::new();
            if let Some(arr) = rules_arr {
                for rule in arr {
                    let ctor = Self::get_u32(rule, "ctor");
                    if let Some(ConstantInfo::Constructor { induct, .. }) = self.env.get(ctor) {
                        if type_names.contains(induct) && !claimed.contains(induct) {
                            claimed.push(*induct);
                        }
                    }
                }
            }
            if claimed.is_empty() && n_rules == 0 {
                for t in &all {
                    if type_names.contains(t) && !claimed.contains(t) {
                        claimed.push(*t);
                    }
                }
                if claimed.is_empty() && !nested {
                    return Err(TcError::Reject(format!(
                        "recursor `{rstr}` does not recursor any type in this inductive group"
                    )));
                }
            }
            for owner in &claimed {
                if !seen_rec_for.insert(*owner) {
                    return Err(TcError::Reject(format!(
                        "duplicate recursor for type {owner}"
                    )));
                }
                self.env.rec_of.insert(*owner, rname);
            }
            let num_motives = Self::get_u32(r, "numMotives");
            let motives_ok = num_motives as usize == all.len()
                || num_motives as usize == type_names.len()
                || (nested && num_motives as usize >= type_names.len());
            if !motives_ok {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` has numMotives={num_motives} but group size is {}",
                    type_names.len()
                )));
            }
            let mut nctors = 0u32;
            for tname in &type_names {
                if let Some(ConstantInfo::InductiveType { ctors, .. }) = self.env.get(*tname) {
                    nctors += ctors.len() as u32;
                }
            }
            let num_minors = Self::get_u32(r, "numMinors");
            let minors_ok = if nested {
                num_minors >= nctors
            } else {
                num_minors == nctors
            };
            if !minors_ok {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` has numMinors={num_minors} but constructor count is {nctors}"
                )));
            }
        }
        {
            // Minor concatenation is Lean's rec_k order (main, then nested
            // types in specialization order). Main = recs in `rec_of` (rule
            // constructors), not the pretty suffix `.rec`. Nested recs with
            // the same container (`Value.rec_3` / `rec_4`, both `List`) share
            // `ctor.induct`; `I.rec_N` is the specialization index — order
            // only, not a reject gate. Unique-container first-occurrence
            // put `List` before `Map` and rejected `Value._sizeOf_5_eq`.
            let mut group: Vec<u32> = recs.iter().map(|r| Self::get_u32(r, "name")).collect();
            group.sort_by_key(|n| {
                let (tag, rec_k) = rec_sort_key(
                    self.names
                        .get(*n as usize)
                        .map(|s| s.as_str())
                        .unwrap_or(""),
                );
                if self.env.rec_of.values().any(|r| r == n) {
                    (0u8, 0u32)
                } else {
                    (tag.saturating_add(1), rec_k)
                }
            });
            for n in &group {
                self.env.rec_group.insert(*n, group.clone());
            }
        }
        for t in &type_names {
            if !self.env.rec_of.contains_key(t) {
                let tstr = self
                    .names
                    .get(*t as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                return Err(TcError::Reject(format!(
                    "inductive `{tstr}` is missing a recursor"
                )));
            }
        }
        Ok(())
    }

    /// Nested specializations actually occurring in constructor fields of
    /// `type_names`, including those found by instantiating a previous
    /// inductive's constructors (Array T also yields List T).
    fn counted_nested(&self, type_names: &[u32]) -> usize {
        let mut seen: FxHashSet<usize> = FxHashSet::default();
        let mut work: Vec<Expr> = Vec::new();
        for &tname in type_names {
            let (ctors, nparams) = match self.env.get(tname) {
                Some(ConstantInfo::InductiveType {
                    ctors, num_params, ..
                }) => (ctors.clone(), *num_params),
                _ => continue,
            };
            for cname in ctors {
                if let Some(ConstantInfo::Constructor { typ, .. }) = self.env.get(cname) {
                    work.extend(ctor_field_tys(typ, nparams, None));
                }
            }
        }
        let mut i = 0;
        while i < work.len() {
            let e = work[i].clone();
            self.collect_nested_in(&e, type_names, &mut seen, &mut work);
            i += 1;
        }
        seen.len()
    }

    fn collect_nested_in(
        &self,
        e: &Expr,
        group: &[u32],
        seen: &mut FxHashSet<usize>,
        work: &mut Vec<Expr>,
    ) {
        match &***e {
            ExprData::App(_, _) => {
                let (h, args) = expr::unfold_apps(e);
                if let ExprData::Const(n, us) = &**h {
                    self.note_nested_app(*n, us.as_slice(), &args, group, seen, work);
                }
                self.collect_nested_in(&h, group, seen, work);
                for a in &args {
                    self.collect_nested_in(a, group, seen, work);
                }
            }
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                self.collect_nested_in(t, group, seen, work);
                self.collect_nested_in(b, group, seen, work);
            }
            ExprData::Let(t, v, b) => {
                self.collect_nested_in(t, group, seen, work);
                self.collect_nested_in(v, group, seen, work);
                self.collect_nested_in(b, group, seen, work);
            }
            ExprData::Proj(_, _, v) => self.collect_nested_in(v, group, seen, work),
            ExprData::Const(n, us) => {
                self.note_nested_app(*n, us.as_slice(), &[], group, seen, work)
            }
            _ => {}
        }
    }

    fn note_nested_app(
        &self,
        n: u32,
        us: &[Level],
        args: &[Expr],
        group: &[u32],
        seen: &mut FxHashSet<usize>,
        work: &mut Vec<Expr>,
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
        if args.len() < num_params as usize {
            return;
        }
        let params = &args[..num_params as usize];
        if !params.iter().any(|a| expr_occurs_names(a, group)) {
            return;
        }
        let all = all.clone();
        for m in all {
            let key_e = expr::apps(expr::const_(m, us.to_vec()), params);
            let k = Rc::as_ptr(&key_e) as usize;
            if !seen.insert(k) {
                continue;
            }
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
                    work.extend(ctor_field_tys(&ty, m_params, Some(params)));
                }
            }
        }
    }

    /// Parse+check the file line by line, checking each declaration as it is
    /// encountered (matching kernel semantics: later decls may depend on
    /// earlier ones). Returns Ok(()) if every checked declaration is accepted.
    pub fn run<R: BufRead>(&mut self, reader: R) -> Result<(), TcError> {
        for line in reader.lines() {
            let line = line.map_err(|e| TcError::Other(format!("io: {e}")))?;
            if line.trim().is_empty() {
                continue;
            }
            let v: Value = serde_json::from_str(&line)
                .map_err(|e| TcError::Other(format!("json parse: {e} on line: {line}")))?;
            self.handle_line(&v)?;
        }
        Ok(())
    }

    fn handle_line(&mut self, v: &Value) -> Result<(), TcError> {
        if v.get("meta").is_some() {
            return Ok(());
        }
        if let Some(idx) = v.get("in").and_then(|x| x.as_u64()) {
            self.handle_name(idx as u32, v);
            return Ok(());
        }
        if let Some(idx) = v.get("il").and_then(|x| x.as_u64()) {
            self.handle_level(idx as u32, v);
            return Ok(());
        }
        if let Some(idx) = v.get("ie").and_then(|x| x.as_u64()) {
            self.handle_expr(idx as u32, v)?;
            return Ok(());
        }
        if let Some(d) = v.get("axiom") {
            self.handle_def_like("axiomDecl", d)?;
            self.check_last(d, "axiom")?;
            return Ok(());
        }
        if let Some(d) = v.get("def") {
            self.handle_def_like("defnDecl", d)?;
            self.check_last(d, "def")?;
            return Ok(());
        }
        if let Some(d) = v.get("thm") {
            self.handle_def_like("thmDecl", d)?;
            self.check_last(d, "theorem")?;
            return Ok(());
        }
        if let Some(d) = v.get("opaque") {
            self.handle_def_like("opaqueDecl", d)?;
            self.check_last(d, "opaque")?;
            return Ok(());
        }
        if let Some(d) = v.get("quot") {
            self.handle_quot(d)?;
            return Ok(());
        }
        if let Some(d) = v.get("inductive") {
            self.handle_inductive_block(d)?;
            let names: Vec<u32> = d
                .get("types")
                .and_then(|x| x.as_array())
                .map(|a| a.iter().map(|t| Self::get_u32(t, "name")).collect())
                .unwrap_or_default();
            let nat_ref = self.name_by_str.get("Nat").copied();
            let string_ref = self.name_by_str.get("String").copied();
            for n in names {
                Checker::new(&self.env, &self.names, nat_ref, string_ref)
                    .check_inductive_group(n)
                    .map_err(|e| self.annotate(n, e))?;
            }
            return Ok(());
        }
        Ok(())
    }

    fn check_last(&mut self, d: &Value, kind: &str) -> Result<(), TcError> {
        let name = Self::require_u32(d, "name")?;
        self.decl_count += 1;
        let nm = self
            .names
            .get(name as usize)
            .map(|s| s.as_str())
            .unwrap_or("?");
        let debug = std::env::var_os("KIOTA_DEBUG").is_some();
        if self.decl_count % 100 == 0
            || std::env::var_os("KIOTA_PROGRESS").is_some()
            || (debug && self.decl_count >= 18_000)
        {
            eprintln!("[decl #{}] {kind} {nm}", self.decl_count);
            let _ = std::io::stderr().flush();
        }
        if std::env::var_os("KIOTA_SIZE_LOG").is_some() {
            let sz = self
                .env
                .get(name)
                .and_then(|c| c.value())
                .map(|v| crate::tc::expr_size_capped(v, 200_000))
                .unwrap_or(0);
            let hint = match self.env.get(name) {
                Some(ConstantInfo::Def {
                    hints: ReducibilityHints::Regular(h),
                    ..
                }) => format!("R{h}"),
                Some(ConstantInfo::Def {
                    hints: ReducibilityHints::Abbrev,
                    ..
                }) => "A".into(),
                Some(ConstantInfo::Def {
                    hints: ReducibilityHints::Opaque,
                    ..
                }) => "O".into(),
                Some(ConstantInfo::Theorem { .. }) => "T".into(),
                _ => "-".into(),
            };
            eprintln!("SIZE #{} {kind} {hint} {sz} {nm}", self.decl_count);
        }
        if std::env::var_os("KIOTA_SIZE_ONLY").is_some() {
            return Ok(());
        }
        if let Ok(max) = std::env::var("KIOTA_MAX_DECL") {
            if let Ok(max_n) = max.parse::<usize>() {
                if self.decl_count > max_n {
                    return Err(TcError::Decline(format!("KIOTA_MAX_DECL={max_n}")));
                }
            }
        }
        if let Ok(min) = std::env::var("KIOTA_MIN_DECL") {
            if let Ok(min_n) = min.parse::<usize>() {
                if self.decl_count < min_n {
                    return Ok(());
                }
            }
        }
        let nat_ref = self.name_by_str.get("Nat").copied();
        let string_ref = self.name_by_str.get("String").copied();
        Checker::new(&self.env, &self.names, nat_ref, string_ref)
            .check_decl(name, kind)
            .map_err(|e| self.annotate(name, e))
    }

    fn annotate(&self, name: u32, e: TcError) -> TcError {
        let nm = self
            .names
            .get(name as usize)
            .map(|s| s.as_str())
            .unwrap_or("?");
        match e {
            TcError::Reject(m) => TcError::Reject(format!("[{nm}] {m}")),
            TcError::Decline(m) => TcError::Decline(format!("[{nm}] {m}")),
            TcError::Other(m) => TcError::Other(format!("[{nm}] {m}")),
        }
    }
}

fn kind_or_direct(_v: &Value) {}

fn pi_telescope_len(typ: &Expr) -> u32 {
    let mut n = 0u32;
    let mut cur = typ.clone();
    loop {
        match &**cur {
            crate::expr::ExprData::Pi(_, _, body) => {
                n += 1;
                cur = body.clone();
            }
            _ => return n,
        }
    }
}

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

fn expr_occurs_names(e: &Expr, names: &[u32]) -> bool {
    match &***e {
        ExprData::Const(n, _) => names.contains(n),
        ExprData::App(f, a) => expr_occurs_names(f, names) || expr_occurs_names(a, names),
        ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
            expr_occurs_names(t, names) || expr_occurs_names(b, names)
        }
        ExprData::Let(t, v, b) => {
            expr_occurs_names(t, names)
                || expr_occurs_names(v, names)
                || expr_occurs_names(b, names)
        }
        ExprData::Proj(_, _, v) => expr_occurs_names(v, names),
        _ => false,
    }
}

fn is_quot_rel(e: &Expr) -> bool {
    match &***e {
        ExprData::Pi(_, _, b1) => match &***b1 {
            ExprData::Pi(_, _, b2) => matches!(&***b2, ExprData::Sort(l) if level::is_zero(l)),
            _ => false,
        },
        _ => false,
    }
}

/// Kernel quot shapes: Type 2-Pi Sort-dom + rel + Sort; Ctor 3-Pi Sort-dom + rel + App; Lift 6; Ind 5.
fn quot_type_matches_kind(kind: &QuotKind, typ: &Expr) -> bool {
    let mut doms: Vec<Expr> = Vec::new();
    let mut cur = typ.clone();
    loop {
        match &**cur {
            ExprData::Pi(_, dom, body) => {
                doms.push(dom.clone());
                cur = body.clone();
            }
            rest => {
                let n = doms.len();
                return match kind {
                    QuotKind::Type => {
                        n == 2
                            && matches!(rest, ExprData::Sort(_))
                            && matches!(&**doms[0], ExprData::Sort(_))
                            && is_quot_rel(&doms[1])
                    }
                    QuotKind::Ctor => {
                        n == 3
                            && matches!(rest, ExprData::App(_, _))
                            && matches!(&**doms[0], ExprData::Sort(_))
                            && is_quot_rel(&doms[1])
                    }
                    QuotKind::Lift => n == 6,
                    QuotKind::Ind => n == 5,
                };
            }
        }
    }
}

/// Lean nested recursor numbering: `.rec` first, then `.rec_1`, `.rec_2`, …
/// Used for rec_group minor order only, not extra-rec reject.
fn rec_sort_key(name: &str) -> (u8, u32) {
    if let Some((_, suf)) = name.rsplit_once(".rec_") {
        if let Ok(n) = suf.parse::<u32>() {
            return (1, n);
        }
        return (2, 0);
    }
    if name.ends_with(".rec") {
        return (0, 0);
    }
    (3, 0)
}
