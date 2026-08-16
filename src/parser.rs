use crate::env::{ConstantInfo, Environment, QuotKind, RecRule, ReducibilityHints};
use crate::expr::{self, BinderInfo, Expr};
use crate::level::{self, Level};
use crate::tc::{Checker, TcError};
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::Value;
use std::io::BufRead;
use std::rc::Rc;

pub struct Parser {
    pub names: Vec<Rc<String>>, // index -> full dotted name (for diagnostics / builtin lookup)
    pub name_by_str: FxHashMap<String, u32>,
    pub levels: Vec<Level>,
    pub exprs: Vec<Expr>,
    pub env: Environment,
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
        Parser {
            names: vec![Rc::new(String::new())], // index 0 = anonymous
            name_by_str: FxHashMap::default(),
            levels: vec![level::zero()], // index 0 = zero
            exprs: Vec::new(),
            env: Environment::default(),
        }
    }

    fn get_u32(v: &Value, k: &str) -> u32 {
        v.get(k).and_then(|x| x.as_u64()).unwrap_or(0) as u32
    }
    fn get_str<'a>(v: &'a Value, k: &str) -> &'a str {
        v.get(k).and_then(|x| x.as_str()).unwrap_or("")
    }
    fn get_bool(v: &Value, k: &str) -> bool {
        v.get(k).and_then(|x| x.as_bool()).unwrap_or(false)
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

    fn handle_expr(&mut self, idx: u32, v: &Value) {
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
            // Unknown expr kind - use a sort as inert placeholder; declarations
            // referencing this will be handled defensively by the checker.
            expr::sort(level::zero())
        };
        while self.exprs.len() <= idx as usize {
            self.exprs.push(expr::sort(level::zero()));
        }
        self.exprs[idx as usize] = e;
    }

    fn hints_of(s: &str, n: u64) -> ReducibilityHints {
        match s {
            "opaque" => ReducibilityHints::Opaque,
            "abbrev" => ReducibilityHints::Abbrev,
            _ => ReducibilityHints::Regular(n as u32),
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
        let name = Self::get_u32(v, "name");
        self.reject_if_dup(name)?;
        let level_params = Self::get_vec_u32(v, "levelParams");
        let typ = self.expr_at(Self::get_u32(v, "type"));
        match kind {
            "axiomDecl" | "axiom" => {
                let is_unsafe = Self::get_bool(v, "isUnsafe");
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
                let value = self.expr_at(Self::get_u32(v, "value"));
                let hints_v = v.get("hints");
                let hints = match hints_v {
                    Some(Value::String(s)) => Self::hints_of(s, 0),
                    Some(Value::Object(o)) => {
                        if let Some(n) = o.get("regular").and_then(|x| x.as_u64()) {
                            ReducibilityHints::Regular(n as u32)
                        } else {
                            ReducibilityHints::Regular(0)
                        }
                    }
                    _ => ReducibilityHints::Regular(0),
                };
                let is_unsafe = Self::get_str(v, "safety") == "unsafe";
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
                let value = self.expr_at(Self::get_u32(v, "value"));
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
                let value = self.expr_at(Self::get_u32(v, "value"));
                let is_unsafe = Self::get_str(v, "safety") == "unsafe";
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
        let kind = match Self::get_str(v, "kind") {
            "type" => QuotKind::Type,
            "ctor" => QuotKind::Ctor,
            "lift" => QuotKind::Lift,
            "ind" => QuotKind::Ind,
            _ => return Ok(()),
        };
        let name = Self::get_u32(v, "name");
        let level_params = Self::get_vec_u32(v, "levelParams");
        let typ = self.expr_at(Self::get_u32(v, "type"));
        self.reject_if_dup(name)?;
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
            let name = Self::get_u32(t, "name");
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(t, "levelParams");
            let typ = self.expr_at(Self::get_u32(t, "type"));
            let num_params = Self::get_u32(t, "numParams");
            let num_indices = Self::get_u32(t, "numIndices");
            let all = Self::get_vec_u32(t, "all");
            let ctor_names = Self::get_vec_u32(t, "ctors");
            let is_rec = Self::get_bool(t, "isRec");
            let is_unsafe = Self::get_bool(t, "isUnsafe");
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
            let name = Self::get_u32(c, "name");
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(c, "levelParams");
            let typ = self.expr_at(Self::get_u32(c, "type"));
            let induct = Self::get_u32(c, "induct");
            let cidx = Self::get_u32(c, "cidx");
            let num_params = Self::get_u32(c, "numParams");
            let num_fields = Self::get_u32(c, "numFields");
            let is_unsafe = Self::get_bool(c, "isUnsafe");
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
            let name = Self::get_u32(r, "name");
            self.reject_if_dup(name)?;
            let level_params = Self::get_vec_u32(r, "levelParams");
            let typ = self.expr_at(Self::get_u32(r, "type"));
            let all = Self::get_vec_u32(r, "all");
            let num_params = Self::get_u32(r, "numParams");
            let num_indices = Self::get_u32(r, "numIndices");
            let num_motives = Self::get_u32(r, "numMotives");
            let num_minors = Self::get_u32(r, "numMinors");
            let k = Self::get_bool(r, "k");
            let is_unsafe = Self::get_bool(r, "isUnsafe");
            let rules = r
                .get("rules")
                .and_then(|x| x.as_array())
                .map(|a| {
                    a.iter()
                        .map(|rule| RecRule {
                            ctor: Self::get_u32(rule, "ctor"),
                            nfields: Self::get_u32(rule, "nfields"),
                            rhs: self.expr_at(Self::get_u32(rule, "rhs")),
                        })
                        .collect()
                })
                .unwrap_or_default();
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

        // Recursor names: each inductive `I` needs `I.rec`. Nested auxiliaries
        // are exported as `I.rec_1`, `I.rec_2`, … — accept those, do not treat
        // them as a second `I.rec`. Exported `k` / rule payloads are not trusted.
        let type_names: Vec<u32> = types.iter().map(|t| Self::get_u32(t, "name")).collect();
        let nested = types.iter().any(|t| Self::get_u32(t, "numNested") > 0);
        let mut seen_rec_for: FxHashSet<u32> = FxHashSet::default();
        for r in &recs {
            let rname = Self::get_u32(r, "name");
            let rstr = self
                .names
                .get(rname as usize)
                .map(|s| s.as_str())
                .unwrap_or("");
            let mut matched = None;
            let mut aux = false;
            for t in &type_names {
                let tstr = self
                    .names
                    .get(*t as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("");
                if rstr == format!("{tstr}.rec") {
                    matched = Some(*t);
                    break;
                }
                let prefix = format!("{tstr}.rec_");
                if rstr.starts_with(&prefix)
                    && rstr[prefix.len()..].bytes().all(|b| b.is_ascii_digit())
                {
                    matched = Some(*t);
                    aux = true;
                    break;
                }
            }
            let Some(t) = matched else {
                return Err(TcError::Reject(format!(
                    "recursor `{rstr}` is not named `I.rec` for an inductive in this group"
                )));
            };
            if !aux {
                if !seen_rec_for.insert(t) {
                    return Err(TcError::Reject(format!("duplicate recursor for type {t}")));
                }
                self.env.rec_of.insert(t, rname);
            }
            let all = Self::get_vec_u32(r, "all");
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
            let mut group: Vec<u32> = recs.iter().map(|r| Self::get_u32(r, "name")).collect();
            group.sort_by_key(|n| {
                rec_sort_key(
                    self.names
                        .get(*n as usize)
                        .map(|s| s.as_str())
                        .unwrap_or(""),
                )
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
                    "inductive `{tstr}` is missing a recursor named `{tstr}.rec`"
                )));
            }
        }
        Ok(())
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
            self.handle_expr(idx as u32, v);
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
        let name = Self::get_u32(d, "name");
        if std::env::var_os("KIOTA_PROGRESS").is_some() {
            static COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let c = COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if c >= 3225 && c <= 3235 {
                let nm = self.names.get(name as usize).map(|s| s.as_str()).unwrap_or("?");
                eprintln!("#{c} {kind} {nm}");
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

/// `.rec` first, then `.rec_1`, `.rec_2`, … so nested minors concatenate
/// as main ctors then nested types in declaration order.
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
