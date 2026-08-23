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
    defined_levels: FxHashSet<u32>,
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
            defined_levels: FxHashSet::from_iter([0]),
            exprs: Vec::new(),
            env: Environment::default(),
            decl_count: 0,
        }
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

    fn require_u32_value(x: &Value, k: &str) -> Result<u32, TcError> {
        match x.as_u64() {
            Some(n) if n <= u32::MAX as u64 => Ok(n as u32),
            _ => Err(TcError::Reject(format!("field `{k}` must be a u32"))),
        }
    }

    fn require_level(&self, i: u32) -> Result<Level, TcError> {
        self.levels
            .get(i as usize)
            .cloned()
            .ok_or_else(|| TcError::Reject(format!("level index {i} is out of range")))
    }

    fn get_str<'a>(v: &'a Value, k: &str) -> &'a str {
        v.get(k).and_then(|x| x.as_str()).unwrap_or("")
    }
    fn bool_if_present(v: &Value, k: &str) -> Result<bool, TcError> {
        match v.get(k) {
            None => Ok(false),
            Some(x) => x
                .as_bool()
                .ok_or_else(|| TcError::Reject(format!("field `{k}` must be a bool"))),
        }
    }
    fn require_bool(v: &Value, k: &str) -> Result<bool, TcError> {
        match v.get(k) {
            None => Err(TcError::Reject(format!("missing required field `{k}`"))),
            Some(x) => x
                .as_bool()
                .ok_or_else(|| TcError::Reject(format!("field `{k}` must be a bool"))),
        }
    }
    fn require_vec_u32(v: &Value, k: &str) -> Result<Vec<u32>, TcError> {
        let values = v
            .get(k)
            .and_then(Value::as_array)
            .ok_or_else(|| TcError::Reject(format!("field `{k}` must be an array")))?;
        values
            .iter()
            .map(|e| Self::require_u32_value(e, k))
            .collect()
    }

    fn require_pair_u32(v: &Value, k: &str) -> Result<(u32, u32), TcError> {
        if let Some(arr) = v.as_array() {
            if arr.len() != 2 {
                return Err(TcError::Reject(format!(
                    "level `{k}` pair must have exactly two entries"
                )));
            }
            Ok((
                Self::require_u32_value(&arr[0], k)?,
                Self::require_u32_value(&arr[1], k)?,
            ))
        } else {
            Ok((Self::require_u32(v, "lhs")?, Self::require_u32(v, "rhs")?))
        }
    }

    fn handle_name(&mut self, idx: u32, v: &Value) -> Result<(), TcError> {
        if idx == 0 {
            return Err(TcError::Reject(
                "name index 0 is reserved for the anonymous name".into(),
            ));
        }
        let full = if let Some(s) = v.get("str") {
            let pre = Self::require_u32(s, "pre")?;
            let seg = s
                .get("str")
                .and_then(Value::as_str)
                .ok_or_else(|| TcError::Reject("name string segment must be a string".into()))?;
            if seg.is_empty() {
                return Err(TcError::Reject("name string segment must not be empty".into()));
            }
            let parent = self
                .names
                .get(pre as usize)
                .ok_or_else(|| TcError::Reject(format!("name parent index {pre} is out of range")))?;
            if pre != 0 && parent.is_empty() {
                return Err(TcError::Reject(format!(
                    "name parent index {pre} is undefined"
                )));
            }
            if parent.is_empty() {
                seg.to_string()
            } else {
                format!("{}.{}", parent, seg)
            }
        } else if let Some(n) = v.get("num") {
            let pre = Self::require_u32(n, "pre")?;
            let i = n
                .get("i")
                .and_then(Value::as_u64)
                .ok_or_else(|| TcError::Reject("numeric name segment must be a u64".into()))?;
            let parent = self
                .names
                .get(pre as usize)
                .ok_or_else(|| TcError::Reject(format!("name parent index {pre} is out of range")))?;
            if pre != 0 && parent.is_empty() {
                return Err(TcError::Reject(format!(
                    "name parent index {pre} is undefined"
                )));
            }
            if parent.is_empty() {
                format!("{}", i)
            } else {
                format!("{}.{}", parent, i)
            }
        } else {
            return Err(TcError::Reject("invalid name record".into()));
        };
        if let Some(previous) = self.name_by_str.get(&full) {
            return Err(TcError::Reject(format!(
                "duplicate fully qualified name `{full}` at indices {previous} and {idx}"
            )));
        }
        while self.names.len() <= idx as usize {
            self.names.push(Rc::new(String::new()));
        }
        if !self.names[idx as usize].is_empty() {
            return Err(TcError::Reject(format!(
                "duplicate name index {idx}"
            )));
        }
        self.name_by_str.insert(full.clone(), idx);
        self.names[idx as usize] = Rc::new(full);
        Ok(())
    }

    fn handle_level(&mut self, idx: u32, v: &Value) -> Result<(), TcError> {
        if idx == 0 || !self.defined_levels.insert(idx) {
            return Err(TcError::Reject(format!(
                "duplicate or reserved level index {idx}"
            )));
        }
        let l = if let Some(a) = v.get("succ") {
            let a = Self::require_u32_value(a, "succ")?;
            level::succ(self.require_level(a)?)
        } else if let Some(m) = v.get("max") {
            let (a, b) = Self::require_pair_u32(m, "max")?;
            level::max(self.require_level(a)?, self.require_level(b)?)
        } else if let Some(m) = v.get("imax") {
            let (a, b) = Self::require_pair_u32(m, "imax")?;
            level::imax(self.require_level(a)?, self.require_level(b)?)
        } else if let Some(p) = v.get("param") {
            let p = Self::require_u32_value(p, "param")?;
            if self.names.get(p as usize).is_none_or(|n| n.is_empty()) {
                return Err(TcError::Reject(format!(
                    "universe parameter name index {p} is undefined"
                )));
            }
            level::param(p)
        } else {
            return Err(TcError::Reject("invalid level record".into()));
        };
        while self.levels.len() <= idx as usize {
            self.levels.push(level::zero());
        }
        self.levels[idx as usize] = l;
        Ok(())
    }

    fn handle_expr(&mut self, idx: u32, v: &Value) -> Result<(), TcError> {
        let e = if let Some(l) = v.get("sort") {
            let i = Self::require_u32_value(l, "sort")?;
            expr::sort(self.require_level(i)?)
        } else if let Some(c) = v.get("const") {
            let name = Self::require_u32(c, "name")?;
            let us = Self::require_vec_u32(c, "us")?
                .into_iter()
                .map(|i| self.require_level(i))
                .collect::<Result<Vec<_>, _>>()?;
            expr::const_(name, us)
        } else if let Some(b) = v.get("bvar") {
            expr::bvar(Self::require_u32_value(b, "bvar")?)
        } else if let Some(a) = v.get("app") {
            let f = self.require_expr(a, "fn")?;
            let x = self.require_expr(a, "arg")?;
            expr::app(f, x)
        } else if let Some(l) = v.get("lam") {
            let bi = bi_of(Self::get_str(l, "binderInfo"));
            Self::require_u32(l, "name")?;
            let ty = self.require_expr(l, "type")?;
            let body = self.require_expr(l, "body")?;
            expr::lam(bi, ty, body)
        } else if let Some(p) = v.get("forallE") {
            let bi = bi_of(Self::get_str(p, "binderInfo"));
            Self::require_u32(p, "name")?;
            let ty = self.require_expr(p, "type")?;
            let body = self.require_expr(p, "body")?;
            expr::pi(bi, ty, body)
        } else if let Some(l) = v.get("letE") {
            Self::require_u32(l, "name")?;
            let ty = self.require_expr(l, "type")?;
            let val = self.require_expr(l, "value")?;
            let body = self.require_expr(l, "body")?;
            expr::let_(ty, val, body)
        } else if let Some(p) = v.get("proj") {
            let s = Self::require_u32(p, "typeName")?;
            let i = Self::require_u32(p, "idx")?;
            let e2 = self.require_expr(p, "struct")?;
            expr::proj(s, i, e2)
        } else if let Some(n) = v.get("natVal") {
            let s = n.as_str().unwrap_or("0");
            let n: BigUint = s.parse().unwrap_or_default();
            expr::lit_nat(n)
        } else if let Some(s) = v.get("strVal") {
            let s = s.as_str().unwrap_or("").to_string();
            expr::lit_str(s)
        } else if let Some(m) = v.get("mdata") {
            self.require_expr(m, "expr")?
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
        let level_params = Self::require_vec_u32(v, "levelParams")?;
        let typ = self.require_expr(v, "type")?;
        // Ordinary declarations are checked in the environment that precedes
        // them. Lean compiles structural recursion through recursors; a raw
        // constant may never occur in its own declared type or value. Since
        // this parser installs the record before `check_last`, reject the
        // otherwise-in-scope cycle explicitly at the boundary.
        if expr_occurs_names(&typ, &[name]) {
            return Err(TcError::Reject(
                "declaration type refers to the declaration being defined".into(),
            ));
        }
        match kind {
            "axiomDecl" | "axiom" => {
                let is_unsafe = Self::require_bool(v, "isUnsafe")?;
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
                if expr_occurs_names(&value, &[name]) {
                    return Err(TcError::Reject(
                        "definition value refers to the declaration being defined".into(),
                    ));
                }
                let hints = Self::require_hints(v)?;
                let safety = Self::get_str(v, "safety");
                if safety == "unsafe" || safety == "partial" {
                    return Err(TcError::Reject(format!("{safety} definition")));
                }
                if Self::bool_if_present(v, "isUnsafe")? {
                    return Err(TcError::Reject("unsafe definition".into()));
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
                if expr_occurs_names(&value, &[name]) {
                    return Err(TcError::Reject(
                        "theorem value refers to the declaration being defined".into(),
                    ));
                }
                if Self::bool_if_present(v, "isUnsafe")? {
                    return Err(TcError::Reject("unsafe theorem".into()));
                }
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
                if expr_occurs_names(&value, &[name]) {
                    return Err(TcError::Reject(
                        "opaque value refers to the declaration being defined".into(),
                    ));
                }
                let safety = Self::get_str(v, "safety");
                if safety == "unsafe" || safety == "partial" {
                    return Err(TcError::Reject(format!("{safety} opaque")));
                }
                let is_unsafe = Self::require_bool(v, "isUnsafe")?;
                if is_unsafe {
                    return Err(TcError::Reject("unsafe opaque".into()));
                }
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
        let level_params = Self::require_vec_u32(v, "levelParams")?;
        let typ = self.require_expr(v, "type")?;
        self.reject_if_dup(name)?;
        if !quot_type_matches_kind(self, &kind, name, &level_params, &typ) {
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
            let level_params = Self::require_vec_u32(t, "levelParams")?;
            let typ = self.require_expr(t, "type")?;
            let num_params = Self::require_u32(t, "numParams")?;
            let num_indices = Self::require_u32(t, "numIndices")?;
            let all = Self::require_vec_u32(t, "all")?;
            let ctor_names = Self::require_vec_u32(t, "ctors")?;
            let is_rec = Self::require_bool(t, "isRec")?;
            let is_unsafe = Self::require_bool(t, "isUnsafe")?;
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
            let level_params = Self::require_vec_u32(c, "levelParams")?;
            let typ = self.require_expr(c, "type")?;
            let induct = Self::require_u32(c, "induct")?;
            let cidx = Self::require_u32(c, "cidx")?;
            let num_params = Self::require_u32(c, "numParams")?;
            let num_fields = Self::require_u32(c, "numFields")?;
            let is_unsafe = Self::require_bool(c, "isUnsafe")?;
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
            let level_params = Self::require_vec_u32(r, "levelParams")?;
            let typ = self.require_expr(r, "type")?;
            let all = Self::require_vec_u32(r, "all")?;
            let num_params = Self::require_u32(r, "numParams")?;
            let num_indices = Self::require_u32(r, "numIndices")?;
            let num_motives = Self::require_u32(r, "numMotives")?;
            let num_minors = Self::require_u32(r, "numMinors")?;
            let k = false;
            let is_unsafe = Self::require_bool(r, "isUnsafe")?;
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
        let type_names: Vec<u32> = types
            .iter()
            .map(|t| Self::require_u32(t, "name"))
            .collect::<Result<_, _>>()?;
        let nested_n = self.counted_nested(&type_names);
        let nested = nested_n > 0;

        // Reconstruct constructor identity from the checked block instead of
        // trusting the redundant export metadata used later by projection and
        // iota reduction.
        let declared_ctor_names: FxHashSet<u32> = ctors
            .iter()
            .map(|c| Self::require_u32(c, "name"))
            .collect::<Result<_, _>>()?;
        if declared_ctor_names.len() != ctors.len() {
            return Err(TcError::Reject(
                "duplicate constructor declaration in inductive group".into(),
            ));
        }
        let mut owned_ctor_names: FxHashSet<u32> = FxHashSet::default();
        for t in &types {
            let tname = Self::require_u32(t, "name")?;
            if Self::require_vec_u32(t, "all")? != type_names {
                return Err(TcError::Reject(
                    "inductive type has inconsistent mutual-group identity".into(),
                ));
            }
            let t_num_params = Self::require_u32(t, "numParams")?;
            let listed = Self::require_vec_u32(t, "ctors")?;
            let mut recursive = false;
            for (expected_cidx, &cname) in listed.iter().enumerate() {
                if !owned_ctor_names.insert(cname) {
                    return Err(TcError::Reject(
                        "constructor is listed more than once in inductive group".into(),
                    ));
                }
                let Some(ConstantInfo::Constructor {
                    typ,
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                    ..
                }) = self.env.get(cname)
                else {
                    return Err(TcError::Reject(
                        "inductive type lists a non-constructor declaration".into(),
                    ));
                };
                if *induct != tname {
                    return Err(TcError::Reject(
                        "constructor owner does not match its inductive type".into(),
                    ));
                }
                if *cidx != expected_cidx as u32 {
                    return Err(TcError::Reject(
                        "constructor index does not match declaration order".into(),
                    ));
                }
                if *num_params != t_num_params {
                    return Err(TcError::Reject(
                        "constructor numParams does not match its inductive type".into(),
                    ));
                }
                let arity = pi_telescope_len(typ);
                if arity < t_num_params || arity - t_num_params != *num_fields {
                    return Err(TcError::Reject(
                        "constructor numFields does not match its checked telescope".into(),
                    ));
                }
                recursive |= ctor_field_tys(typ, t_num_params, None)
                    .iter()
                    .any(|field| expr_occurs_names(field, &type_names));
            }
            if Self::require_bool(t, "isRec")? != recursive {
                return Err(TcError::Reject(
                    "inductive isRec does not match its constructor fields".into(),
                ));
            }
        }
        if owned_ctor_names != declared_ctor_names {
            return Err(TcError::Reject(
                "constructor declarations do not match inductive constructor lists".into(),
            ));
        }

        let expected_recs = type_names.len() + nested_n;
        if recs.len() > expected_recs {
            return Err(TcError::Reject(format!(
                "extra recursor in inductive group ({} recs, expected {expected_recs})",
                recs.len()
            )));
        }

        // Recursor names are declaration identity, not presentation metadata.
        // Lean exports one `I.rec` for every type in the mutual group. Nested
        // specializations are named `I.rec_1`, `I.rec_2`, ... contiguously for
        // whichever group type owns them. Accepting an arbitrary name here
        // lets an export install a second recursor while an unrelated
        // declaration already occupies the canonical `I.rec` name.
        let mut main_rec_seen: FxHashSet<u32> = FxHashSet::default();
        let mut nested_rec_seen: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for r in &recs {
            let rname = Self::require_u32(r, "name")?;
            let rstr = self
                .names
                .get(rname as usize)
                .map(|s| s.as_str())
                .unwrap_or("");
            let mut owner = None;
            for &tname in &type_names {
                let tstr = self
                    .names
                    .get(tname as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("");
                let main = format!("{tstr}.rec");
                if rstr == main {
                    main_rec_seen.insert(tname);
                    owner = Some(tname);
                    break;
                }
            }
            if owner.is_none() {
                for &tname in &type_names {
                    let tstr = self
                        .names
                        .get(tname as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("");
                    let prefix = format!("{tstr}.rec_");
                    let Some(suffix) = rstr.strip_prefix(&prefix) else {
                        continue;
                    };
                    let Ok(n) = suffix.parse::<u32>() else {
                        continue;
                    };
                    if n > 0 && suffix == n.to_string() {
                        nested_rec_seen.entry(tname).or_default().push(n);
                        owner = Some(tname);
                        break;
                    }
                }
            }
            if owner.is_none() {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` does not have a canonical name for its inductive group"
                )));
            }
        }
        for &tname in &type_names {
            let tstr = self
                .names
                .get(tname as usize)
                .map(|s| s.as_str())
                .unwrap_or("?");
            if !main_rec_seen.contains(&tname) {
                return Err(TcError::Reject(format!(
                    "inductive `{tstr}` is missing its canonical recursor `{tstr}.rec`"
                )));
            }
            if let Some(suffixes) = nested_rec_seen.get_mut(&tname) {
                suffixes.sort_unstable();
                for (i, &suffix) in suffixes.iter().enumerate() {
                    let expected = i as u32 + 1;
                    if suffix != expected {
                        return Err(TcError::Reject(format!(
                            "nested recursors for inductive `{tstr}` are not contiguous at `{tstr}.rec_{expected}`"
                        )));
                    }
                }
            }
        }

        // Exported rule RHS terms are never used for reduction, but the rule
        // constructor list selects the minor premise.  Reconstruct that list
        // from declaration identity and constructor order so a forged export
        // cannot swap or omit minors while retaining a well-formed recursor
        // telescope.
        let mut total_rule_count = 0usize;
        for r in &recs {
            let rname = Self::require_u32(r, "name")?;
            let rstr = self
                .names
                .get(rname as usize)
                .map(|s| s.as_str())
                .unwrap_or("");
            let rules = r
                .get("rules")
                .and_then(Value::as_array)
                .ok_or_else(|| TcError::Reject(format!("recursor `{rstr}` rules must be an array")))?;
            let main_owner = type_names.iter().copied().find(|tname| {
                let tstr = self
                    .names
                    .get(*tname as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("");
                rstr == format!("{tstr}.rec")
            });
            let is_main = main_owner.is_some();
            let rule_owner = if let Some(owner) = main_owner {
                owner
            } else {
                let first_ctor = rules
                    .first()
                    .ok_or_else(|| TcError::Reject(format!(
                        "nested recursor `{rstr}` has no constructor rules"
                    )))
                    .and_then(|rule| Self::require_u32(rule, "ctor"))?;
                match self.env.get(first_ctor) {
                    Some(ConstantInfo::Constructor { induct, .. }) => *induct,
                    _ => {
                        return Err(TcError::Reject(format!(
                            "recursor `{rstr}` rule does not name a constructor"
                        )))
                    }
                }
            };
            let expected_ctors = match self.env.get(rule_owner) {
                Some(ConstantInfo::InductiveType { ctors, .. }) => ctors,
                _ => {
                    return Err(TcError::Reject(format!(
                        "recursor `{rstr}` rule owner is not an inductive type"
                    )))
                }
            };
            if rules.is_empty() && is_main {
                // Older minimized fixtures omit redundant main-rec rules.
                // Reduction already derives their order from the inductive's
                // checked constructor list.
                total_rule_count += expected_ctors.len();
                continue;
            }
            if rules.len() != expected_ctors.len() {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` rule count does not match its constructor count"
                )));
            }
            for (rule, expected_ctor) in rules.iter().zip(expected_ctors.iter()) {
                let actual_ctor = Self::require_u32(rule, "ctor")?;
                if actual_ctor != *expected_ctor {
                    return Err(TcError::Reject(format!(
                        "recursor `{rstr}` rule order does not match constructor order"
                    )));
                }
                let expected_fields = match self.env.get(*expected_ctor) {
                    Some(ConstantInfo::Constructor { num_fields, .. }) => *num_fields,
                    _ => unreachable!(),
                };
                if Self::require_u32(rule, "nfields")? != expected_fields {
                    return Err(TcError::Reject(format!(
                        "recursor `{rstr}` rule field count does not match its constructor"
                    )));
                }
            }
            total_rule_count += rules.len();
        }
        for r in &recs {
            let rname = Self::require_u32(r, "name")?;
            let declared = Self::require_u32(r, "numMinors")? as usize;
            if declared != total_rule_count {
                return Err(TcError::Reject(format!(
                    "recursor `{}` numMinors does not match reconstructed group rule count",
                    self.names
                        .get(rname as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
        }

        let mut seen_rec_for: FxHashSet<u32> = FxHashSet::default();
        for r in &recs {
            let rname = Self::require_u32(r, "name")?;
            let rstr = self
                .names
                .get(rname as usize)
                .map(|s| s.as_str())
                .unwrap_or("");
            let all = Self::require_vec_u32(r, "all")?;
            let rules_arr = r.get("rules").and_then(|x| x.as_array());
            let n_rules = rules_arr.map(|a| a.len()).unwrap_or(0);
            let mut claimed: Vec<u32> = Vec::new();
            if let Some(arr) = rules_arr {
                for rule in arr {
                    let ctor = Self::require_u32(rule, "ctor")?;
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
            let num_motives = Self::require_u32(r, "numMotives")?;
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
            let num_minors = Self::require_u32(r, "numMinors")?;
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
            let mut group: Vec<u32> = recs
                .iter()
                .map(|r| Self::require_u32(r, "name"))
                .collect::<Result<_, _>>()?;
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
        if v.get("in").is_some() {
            let idx = Self::require_u32(v, "in")?;
            self.handle_name(idx, v)?;
            return Ok(());
        }
        if v.get("il").is_some() {
            let idx = Self::require_u32(v, "il")?;
            self.handle_level(idx, v)?;
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
            let names: Vec<u32> = match d.get("types").and_then(|x| x.as_array()) {
                Some(a) => a
                    .iter()
                    .map(|t| Self::require_u32(t, "name"))
                    .collect::<Result<_, _>>()?,
                None => Vec::new(),
            };
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
            .map_err(|e| self.annotate(name, e))?;
        let native_nat = Checker::new(&self.env, &self.names, nat_ref, string_ref)
            .authenticate_native_nat_decl(name)
            .map_err(|e| self.annotate(name, e))?;
        if native_nat {
            self.env.native_nat_ops.insert(name);
        }
        Ok(())
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

/// The four quotient declarations are kernel primitives. Their canonical
/// names, universe parameters, dependencies, binder information, and complete
/// types must match Lean's declarations exactly; a telescope length is not an
/// identity check.
fn quot_type_matches_kind(
    parser: &Parser,
    kind: &QuotKind,
    name: u32,
    level_params: &[u32],
    typ: &Expr,
) -> bool {
    let expected_name = match kind {
        QuotKind::Type => "Quot",
        QuotKind::Ctor => "Quot.mk",
        QuotKind::Lift => "Quot.lift",
        QuotKind::Ind => "Quot.ind",
    };
    if parser.names.get(name as usize).map(|s| s.as_str()) != Some(expected_name) {
        return false;
    }
    let expected_levels = if matches!(kind, QuotKind::Lift) { 2 } else { 1 };
    if level_params.len() != expected_levels {
        return false;
    }

    let quot = match parser.name_by_str.get("Quot").copied() {
        Some(n) => n,
        None if matches!(kind, QuotKind::Type) => name,
        None => return false,
    };
    if !matches!(kind, QuotKind::Type)
        && !matches!(
            parser.env.get(quot),
            Some(ConstantInfo::Quot {
                kind: QuotKind::Type,
                ..
            })
        )
    {
        return false;
    }
    let quot_mk = parser.name_by_str.get("Quot.mk").copied();
    if matches!(kind, QuotKind::Ind)
        && !matches!(
            quot_mk.and_then(|n| parser.env.get(n)),
            Some(ConstantInfo::Quot {
                kind: QuotKind::Ctor,
                ..
            })
        )
    {
        return false;
    }

    let u = level::param(level_params[0]);
    let sort_u = expr::sort(u.clone());
    let sort_0 = expr::sort(level::zero());
    let rel = expr::pi(
        BinderInfo::Default,
        expr::bvar(0),
        expr::pi(BinderInfo::Default, expr::bvar(1), sort_0.clone()),
    );
    let expected = match kind {
        QuotKind::Type => expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(),
            expr::pi(BinderInfo::Default, rel.clone(), sort_u),
        ),
        QuotKind::Ctor => {
            let result = expr::apps(
                expr::const_(quot, vec![u.clone()]),
                &[expr::bvar(2), expr::bvar(1)],
            );
            expr::pi(
                BinderInfo::Implicit,
                sort_u,
                expr::pi(
                    BinderInfo::Default,
                    rel.clone(),
                    expr::pi(BinderInfo::Default, expr::bvar(1), result),
                ),
            )
        }
        QuotKind::Lift => {
            let Some(eq) = parser.name_by_str.get("Eq").copied() else {
                return false;
            };
            let v = level::param(level_params[1]);
            let f_dom = expr::pi(BinderInfo::Default, expr::bvar(2), expr::bvar(1));
            let rel_ab = expr::apps(expr::bvar(4), &[expr::bvar(1), expr::bvar(0)]);
            let fa = expr::app(expr::bvar(3), expr::bvar(2));
            let fb = expr::app(expr::bvar(3), expr::bvar(1));
            let eq_fa_fb = expr::apps(expr::const_(eq, vec![v.clone()]), &[expr::bvar(4), fa, fb]);
            let respects = expr::pi(
                BinderInfo::Default,
                expr::bvar(3),
                expr::pi(
                    BinderInfo::Default,
                    expr::bvar(4),
                    expr::pi(BinderInfo::Default, rel_ab, eq_fa_fb),
                ),
            );
            let q_dom = expr::apps(
                expr::const_(quot, vec![u.clone()]),
                &[expr::bvar(4), expr::bvar(3)],
            );
            expr::pi(
                BinderInfo::Implicit,
                sort_u,
                expr::pi(
                    BinderInfo::Implicit,
                    rel.clone(),
                    expr::pi(
                        BinderInfo::Implicit,
                        expr::sort(v),
                        expr::pi(
                            BinderInfo::Default,
                            f_dom,
                            expr::pi(
                                BinderInfo::Default,
                                respects,
                                expr::pi(BinderInfo::Default, q_dom, expr::bvar(3)),
                            ),
                        ),
                    ),
                ),
            )
        }
        QuotKind::Ind => {
            let Some(quot_mk) = quot_mk else {
                return false;
            };
            let beta_dom = expr::pi(
                BinderInfo::Default,
                expr::apps(
                    expr::const_(quot, vec![u.clone()]),
                    &[expr::bvar(1), expr::bvar(0)],
                ),
                sort_0,
            );
            let mk_a = expr::apps(
                expr::const_(quot_mk, vec![u.clone()]),
                &[expr::bvar(3), expr::bvar(2), expr::bvar(0)],
            );
            let h_dom = expr::pi(
                BinderInfo::Default,
                expr::bvar(2),
                expr::app(expr::bvar(1), mk_a),
            );
            let q_dom = expr::apps(expr::const_(quot, vec![u]), &[expr::bvar(3), expr::bvar(2)]);
            expr::pi(
                BinderInfo::Implicit,
                sort_u,
                expr::pi(
                    BinderInfo::Implicit,
                    rel,
                    expr::pi(
                        BinderInfo::Implicit,
                        beta_dom,
                        expr::pi(
                            BinderInfo::Default,
                            h_dom,
                            expr::pi(
                                BinderInfo::Default,
                                q_dom,
                                expr::app(expr::bvar(2), expr::bvar(0)),
                            ),
                        ),
                    ),
                ),
            )
        }
    };
    Rc::ptr_eq(typ, &expected)
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
