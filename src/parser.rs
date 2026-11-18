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
    /// Canonical name index -> the name, rendered by `render_str_component` so
    /// that two different names never render alike. The slot of an index
    /// that has no name line yet, or that is a second index for a name
    /// (see `name_canon`), holds the empty string; the checker never sees
    /// such an index.
    pub names: Vec<Rc<String>>,
    /// Rendered name -> its canonical index. One entry per name.
    pub name_by_str: FxHashMap<String, u32>,
    /// Export name index -> canonical index, `NO_NAME` before the index's
    /// name line. The kernel's identity for a constant, a universe
    /// parameter or a structure is its name, and the export may give one
    /// name several indices (lean4export never does). Every name index
    /// read from the export goes through this table, so the environment,
    /// the expressions and the levels only ever hold the first index a
    /// name was given.
    name_canon: Vec<u32>,
    /// How many export indices are a second index for their name. With any,
    /// the pre-pass's "no expression refers to this constant" is not about
    /// names any more, and `release_theorem_value` stops relying on it.
    aliased_names: u32,
    /// The export's levels by index; `None` before the index's `il` line.
    pub levels: Vec<Option<Level>>,
    /// The export's expression nodes by index. A slot is `None` before its
    /// `ie` line and again after `lifetimes` has released it.
    pub exprs: Vec<Option<Expr>>,
    pub env: Environment,
    pub decl_count: usize,
    /// Last references of the expression indices, from `lifetime::scan`;
    /// `None` keeps every node (stdin input, or `KIOTA_KEEP_EXPORT_NODES`).
    pub lifetimes: Option<crate::lifetime::Lifetimes>,
    /// Lines read so far, counted like `lifetime::scan` counts them.
    pub line_no: u32,
    /// Released theorem proofs, on disk (`run_file` only). `None` keeps
    /// unreleased proofs in memory under the reference policy.
    pub proofs: Option<crate::proofstore::ProofStore>,
}

/// Undo only writes made by the current inductive block. The journal owns
/// replaced values rather than cloning the environment, so importing a block
/// does not copy any earlier declarations. Reverse replay also preserves prior
/// entries if a partially checked block fails after updating ownership maps.
#[derive(Default)]
struct InductiveUndo(Vec<InductiveWrite>);

enum InductiveWrite {
    Constant(u32, Option<ConstantInfo>),
    Owner(u32, Option<u32>),
    Group(u32, Option<Vec<u32>>),
}

impl InductiveUndo {
    fn insert_constant(&mut self, env: &mut Environment, name: u32, value: ConstantInfo) {
        self.0
            .push(InductiveWrite::Constant(name, env.consts.insert(name, value)));
    }

    fn insert_owner(&mut self, env: &mut Environment, name: u32, recursor: u32) {
        self.0
            .push(InductiveWrite::Owner(name, env.rec_of.insert(name, recursor)));
    }

    fn insert_group(&mut self, env: &mut Environment, name: u32, group: Vec<u32>) {
        self.0
            .push(InductiveWrite::Group(name, env.rec_group.insert(name, group)));
    }

    fn rollback(self, env: &mut Environment) {
        fn restore<T>(map: &mut FxHashMap<u32, T>, name: u32, prior: Option<T>) {
            match prior {
                Some(value) => {
                    map.insert(name, value);
                }
                None => {
                    map.remove(&name);
                }
            }
        }
        for write in self.0.into_iter().rev() {
            match write {
                InductiveWrite::Constant(name, prior) => restore(&mut env.consts, name, prior),
                InductiveWrite::Owner(name, prior) => restore(&mut env.rec_of, name, prior),
                InductiveWrite::Group(name, prior) => restore(&mut env.rec_group, name, prior),
            }
        }
    }
}

/// `name_canon` entry of an index no name line has defined.
const NO_NAME: u32 = u32::MAX;

/// A bound variable index no binder can reach. The export's de Bruijn
/// indices are natural numbers; one that does not fit is read as this, so
/// the node stays loose under any number of binders an export can nest and
/// is rejected where a declaration uses it (`loose_of` adds one, which
/// `u32::MAX` itself would wrap to "closed").
const BVAR_UNBOUND: u32 = u32::MAX - 1;

/// One component of a name, rendered so that the dotted rendering of a
/// whole name determines the name: a `Name.str` component is written as it
/// is unless that could be read as something else (it is empty, has a dot,
/// has a guillemet, or is all digits like a `Name.num` component), in which
/// case it is quoted in `«»` with `»` doubled. The by-name lookups
/// (`Nat.succ`, `Quot.mk`, `Eq`, `I.rec`, ...) compare renderings, so the
/// one-component name `«Nat.succ»` and the numeral-named `Foo.«0»` are not
/// `Nat.succ` and `Foo.0`.
fn render_str_component(seg: &str) -> String {
    let plain = !seg.is_empty()
        && !seg.contains(['.', '«', '»'])
        && !seg.bytes().all(|b| b.is_ascii_digit());
    if plain {
        seg.to_string()
    } else {
        format!("«{}»", seg.replace('»', "»»"))
    }
}

/// A numeral as lean4export's reader takes it (`String.toNat?`, Lean
/// 4.35): decimal digits, with single underscores allowed between digits.
/// Anything else is not a numeral; it is not read as zero, and a sign or a
/// trailing separator is not dropped.
fn parse_nat_literal(s: &str) -> Option<BigUint> {
    let mut last_was_digit = false;
    let mut separators = false;
    for b in s.bytes() {
        if b == b'_' {
            if !last_was_digit {
                return None;
            }
            last_was_digit = false;
            separators = true;
        } else if b.is_ascii_digit() {
            last_was_digit = true;
        } else {
            return None;
        }
    }
    if !last_was_digit {
        return None;
    }
    if separators {
        s.replace('_', "").parse().ok()
    } else {
        s.parse().ok()
    }
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
            name_canon: vec![0],
            aliased_names: 0,
            levels: vec![Some(level::zero())], // index 0 = zero
            exprs: Vec::new(),
            env: Environment::default(),
            decl_count: 0,
            lifetimes: None,
            line_no: 0,
            proofs: None,
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

    /// A declaration's type or value. Each is a closed term in the kernel;
    /// a loose bound variable is a malformed declaration, which the
    /// official kernel rejects when its type checker meets the variable.
    fn require_expr(&self, v: &Value, k: &str) -> Result<Expr, TcError> {
        let i = Self::require_u32(v, k)?;
        let e = match self.exprs.get(i as usize) {
            Some(Some(e)) => e.clone(),
            Some(None) => return Err(Self::released(i)),
            None => return Err(TcError::Reject(format!("expr index {i} for `{k}` is out of range"))),
        };
        if !expr::is_closed(&e) {
            let range = expr::loose_bvar_range(&e);
            // `BVAR_UNBOUND` under however many binders the term has.
            if range > u32::MAX / 2 {
                return Err(TcError::Reject(format!(
                    "`{k}` has a bound variable whose index no binder can reach"
                )));
            }
            return Err(TcError::Reject(format!(
                "`{k}` has a loose bound variable (#{})",
                range - 1
            )));
        }
        Ok(e)
    }

    /// Every universe parameter a declaration's expressions mention must be
    /// one of its own `levelParams`, as the official kernel's `check_level`
    /// demands of every `Sort` and constant it infers. A stray parameter is
    /// not a closed universe: it is captured by whichever later declaration
    /// happens to declare that name and instantiates it.
    fn check_universe_params(&self, level_params: &[u32], fields: &[(&str, &Expr)]) -> Result<(), TcError> {
        let mut seen = FxHashSet::default();
        for (k, e) in fields {
            if let Some(p) = expr::undeclared_level_param(e, level_params, &mut seen) {
                return Err(TcError::Reject(format!(
                    "`{k}` mentions the undeclared universe parameter `{}`",
                    self.name_str(p)
                )));
            }
        }
        Ok(())
    }

    /// An exported recursor rule's body. Nothing reduces with it: the
    /// checker derives iota from the inductive declaration itself (field
    /// order, K-likeness), as the official kernel does, so the body is
    /// read like the other export fields it does not trust, open or not.
    fn require_rule_body(&self, rule: &Value) -> Result<Expr, TcError> {
        let i = Self::require_u32(rule, "rhs")?;
        match self.exprs.get(i as usize) {
            Some(Some(e)) => Ok(e.clone()),
            Some(None) => Err(Self::released(i)),
            None => Err(TcError::Reject(format!("expr index {i} for `rhs` is out of range"))),
        }
    }

    /// A reference the lifetime pre-pass did not see. The two passes read
    /// the same fields, so this is a bug; it must surface as an error and
    /// never as a wrong term.
    fn released(i: u32) -> TcError {
        TcError::Other(format!("expr index {i} was released after what the pre-pass took for its last reference"))
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
    /// A table index given directly as a JSON value (`"succ": 3`, an entry
    /// of `"us"`). Like `require_u32`, nothing is defaulted or truncated:
    /// `4294967296` is not index 0.
    fn index_of(x: &Value, what: &str) -> Result<u32, TcError> {
        match x.as_u64() {
            Some(n) if n <= u32::MAX as u64 => Ok(n as u32),
            _ => Err(TcError::Reject(format!("{what} must be a u32 index"))),
        }
    }

    /// The two level indices of a `max`/`imax` record.
    fn pair_u32(v: &Value, what: &str) -> Result<(u32, u32), TcError> {
        match v.as_array().map(|a| a.as_slice()) {
            Some([a, b]) => Ok((Self::index_of(a, what)?, Self::index_of(b, what)?)),
            _ => Err(TcError::Reject(format!("{what} must be a pair of level indices"))),
        }
    }

    /// The name an export index stands for, as its canonical index. An
    /// index is usable only after its name line.
    fn name_at(&self, i: u32) -> Result<u32, TcError> {
        match self.name_canon.get(i as usize) {
            Some(&c) if c != NO_NAME => Ok(c),
            _ => Err(TcError::Reject(format!("name index {i} is used before its name line"))),
        }
    }

    fn require_name(&self, v: &Value, k: &str) -> Result<u32, TcError> {
        self.name_at(Self::require_u32(v, k)?)
    }

    /// A list of names (`levelParams`, `all`, `ctors`). An absent list is
    /// empty; one that is there must be an array of defined name indices.
    fn name_list(&self, v: &Value, k: &str) -> Result<Vec<u32>, TcError> {
        match v.get(k) {
            None => Ok(Vec::new()),
            Some(Value::Array(a)) => a
                .iter()
                .map(|x| self.name_at(Self::index_of(x, &format!("an entry of `{k}`"))?))
                .collect(),
            Some(_) => Err(TcError::Reject(format!("field `{k}` must be an array of name indices"))),
        }
    }

    fn level_at(&self, i: u32) -> Result<Level, TcError> {
        match self.levels.get(i as usize) {
            Some(Some(l)) => Ok(l.clone()),
            _ => Err(TcError::Reject(format!("level index {i} is used before its level line"))),
        }
    }
    fn expr_at(&self, i: u32) -> Result<Expr, TcError> {
        match self.exprs.get(i as usize) {
            Some(Some(e)) => Ok(e.clone()),
            Some(None) => Err(Self::released(i)),
            None => Err(TcError::Reject(format!("expr index {i} is out of range"))),
        }
    }
    /// The expression a record's field `k` refers to.
    fn expr_field(&self, v: &Value, k: &str) -> Result<Expr, TcError> {
        self.expr_at(Self::require_u32(v, k)?)
    }

    /// A name line fixes what its index means, once. The prefix must have
    /// its own line already (index 0 is the anonymous name): a name spelled
    /// while its prefix slot was still empty used to be read as its bare
    /// last component, so that `Foo.Nat` was `Nat`. A second line for an
    /// index must give the same name again: the environment is keyed by
    /// index while the literal types, the `Nat` extensions, the quotient
    /// primitives and `Eq` are found by name, so a line that renamed an
    /// index turned whatever was declared under it into one of those. In
    /// the official kernel a name is its components and nothing renames a
    /// constant.
    ///
    /// Two indices may carry one name; the second is then only another way
    /// to write the first (`name_canon`).
    fn handle_name(&mut self, v: &Value) -> Result<(), TcError> {
        let idx = Self::require_u32(v, "in")?;
        if idx == NO_NAME {
            return Err(TcError::Reject(format!("name index {idx} is out of range")));
        }
        let (pre, component) = if let Some(s) = v.get("str") {
            let seg = s
                .get("str")
                .and_then(|x| x.as_str())
                .ok_or_else(|| TcError::Reject("name line: `str` must be a string".into()))?;
            (Self::require_u32(s, "pre")?, render_str_component(seg))
        } else if let Some(n) = v.get("num") {
            let i = match n.get("i") {
                Some(Value::Number(i)) if i.is_u64() => i.to_string(),
                _ => return Err(TcError::Reject("name line: `i` must be a natural number".into())),
            };
            (Self::require_u32(n, "pre")?, i)
        } else {
            return Err(TcError::Reject("name line is neither `str` nor `num`".into()));
        };
        let parent = match self.name_canon.get(pre as usize) {
            Some(&c) if c != NO_NAME => c,
            _ => {
                return Err(TcError::Reject(format!(
                    "name index {idx} has prefix {pre}, which has no name line yet"
                )))
            }
        };
        let full = if parent == 0 {
            component
        } else {
            format!("{}.{}", self.names[parent as usize], component)
        };
        if self.name_canon.len() <= idx as usize {
            self.name_canon.resize(idx as usize + 1, NO_NAME);
            self.names.resize(idx as usize + 1, self.names[0].clone());
        }
        // The index that already stands for this name, if the name has one.
        let known = self.name_by_str.get(&full).copied();
        match self.name_canon[idx as usize] {
            NO_NAME => match known {
                Some(first) => {
                    self.name_canon[idx as usize] = first;
                    self.aliased_names += 1;
                }
                None => {
                    self.name_canon[idx as usize] = idx;
                    self.names[idx as usize] = Rc::new(full.clone());
                    self.name_by_str.insert(full, idx);
                }
            },
            prev if known == Some(prev) => {}
            prev => {
                let was = if prev == 0 { "the anonymous name" } else { self.names[prev as usize].as_str() };
                return Err(TcError::Reject(format!(
                    "name index {idx} is {was}; a second name line spells it `{full}`"
                )));
            }
        }
        Ok(())
    }

    fn handle_level(&mut self, v: &Value) -> Result<(), TcError> {
        let idx = Self::require_u32(v, "il")?;
        let l = if let Some(a) = v.get("succ") {
            level::succ(self.level_at(Self::index_of(a, "`succ`")?)?)
        } else if let Some(m) = v.get("max") {
            let (a, b) = Self::pair_u32(m, "`max`")?;
            level::max(self.level_at(a)?, self.level_at(b)?)
        } else if let Some(m) = v.get("imax") {
            let (a, b) = Self::pair_u32(m, "`imax`")?;
            level::imax(self.level_at(a)?, self.level_at(b)?)
        } else if let Some(p) = v.get("param") {
            level::param(self.name_at(Self::index_of(p, "`param`")?)?)
        } else {
            return Err(TcError::Reject("unknown level kind".into()));
        };
        if self.levels.len() <= idx as usize {
            self.levels.resize(idx as usize + 1, None);
        }
        self.levels[idx as usize] = Some(l);
        Ok(())
    }

    /// A binder's name is not part of the term, but the index is a name
    /// reference like any other and must have its line.
    fn check_binder_name(&self, b: &Value) -> Result<(), TcError> {
        match b.get("name") {
            None => Ok(()),
            Some(n) => self.name_at(Self::index_of(n, "binder `name`")?).map(|_| ()),
        }
    }

    fn handle_expr(&mut self, v: &Value) -> Result<(), TcError> {
        let idx = Self::require_u32(v, "ie")?;
        let e = if let Some(l) = v.get("sort") {
            expr::sort(self.level_at(Self::index_of(l, "`sort`")?)?)
        } else if let Some(c) = v.get("const") {
            let name = self.require_name(c, "name")?;
            let us = match c.get("us") {
                None => Vec::new(),
                Some(Value::Array(us)) => us
                    .iter()
                    .map(|u| self.level_at(Self::index_of(u, "an entry of `us`")?))
                    .collect::<Result<_, _>>()?,
                Some(_) => return Err(TcError::Reject("field `us` must be an array of level indices".into())),
            };
            expr::const_(name, us)
        } else if let Some(b) = v.get("bvar") {
            match b.as_u64() {
                Some(i) => expr::bvar(i.min(BVAR_UNBOUND as u64) as u32),
                None => return Err(TcError::Reject("`bvar` must be a natural number".into())),
            }
        } else if let Some(a) = v.get("app") {
            let f = self.expr_field(a, "fn")?;
            let x = self.expr_field(a, "arg")?;
            expr::app(f, x)
        } else if let Some(l) = v.get("lam") {
            self.check_binder_name(l)?;
            let bi = bi_of(Self::get_str(l, "binderInfo"));
            let ty = self.expr_field(l, "type")?;
            let body = self.expr_field(l, "body")?;
            expr::lam(bi, ty, body)
        } else if let Some(p) = v.get("forallE") {
            self.check_binder_name(p)?;
            let bi = bi_of(Self::get_str(p, "binderInfo"));
            let ty = self.expr_field(p, "type")?;
            let body = self.expr_field(p, "body")?;
            expr::pi(bi, ty, body)
        } else if let Some(l) = v.get("letE") {
            self.check_binder_name(l)?;
            let ty = self.expr_field(l, "type")?;
            let val = self.expr_field(l, "value")?;
            let body = self.expr_field(l, "body")?;
            expr::let_(ty, val, body)
        } else if let Some(p) = v.get("proj") {
            let s = self.require_name(p, "typeName")?;
            let i = Self::require_u32(p, "idx")?;
            let e2 = self.expr_field(p, "struct")?;
            expr::proj(s, i, e2)
        } else if let Some(n) = v.get("natVal") {
            let n = n
                .as_str()
                .and_then(parse_nat_literal)
                .ok_or_else(|| TcError::Reject("`natVal` must be a string of decimal digits".into()))?;
            expr::lit_nat(n)
        } else if let Some(s) = v.get("strVal") {
            let s = s
                .as_str()
                .ok_or_else(|| TcError::Reject("`strVal` must be a string".into()))?
                .to_string();
            expr::lit_str(s)
        } else if let Some(m) = v.get("mdata") {
            // Metadata wraps an expr; ignore metadata, use inner expr.
            self.expr_field(m, "expr")?
        } else {
            return Err(TcError::Reject("unknown expr kind".into()));
        };
        while self.exprs.len() <= idx as usize {
            self.exprs.push(None);
        }
        self.exprs[idx as usize] = Some(e);
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

    /// A declaration's name must be new. `name` is canonical, so this is
    /// about the name and not about the index the record happened to use.
    /// It is read off the environment, so a rolled-back inductive block
    /// leaves nothing behind.
    fn reject_if_dup(&self, name: u32) -> Result<(), TcError> {
        if self.env.get(name).is_some() {
            return Err(TcError::Reject(format!("duplicate declaration of {}", self.name_str(name))));
        }
        Ok(())
    }

    /// The declaration named `s`, if there is one: what the by-name lookups
    /// (`Nat` and `String` literals, the quotient primitives, `Eq`) resolve
    /// through. `s` is a rendering as in `names`; a name that merely has a
    /// name line is not a constant.
    fn declared(&self, s: &str) -> Option<u32> {
        self.name_by_str.get(s).copied().filter(|i| self.env.get(*i).is_some())
    }

    /// A checker over the current environment.
    fn checker(&self) -> Checker<'_> {
        Checker::new(&self.env, &self.names, self.declared("Nat"), self.declared("String"))
            .with_name_index(&self.name_by_str)
            .with_proof_store(self.proofs.as_ref())
    }

    fn handle_def_like(&mut self, kind: &str, v: &Value) -> Result<(), TcError> {
        let name = self.require_name(v, "name")?;
        self.reject_if_dup(name)?;
        let level_params = self.name_list(v, "levelParams")?;
        let typ = self.require_expr(v, "type")?;
        self.check_universe_params(&level_params, &[("type", &typ)])?;
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
                self.check_universe_params(&level_params, &[("type", &typ), ("value", &value)])?;
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
                self.check_universe_params(&level_params, &[("type", &typ), ("value", &value)])?;
                self.env.insert(
                    name,
                    ConstantInfo::Theorem {
                        level_params,
                        typ,
                        value: Some(value),
                    },
                );
            }
            "opaqueDecl" | "opaque" => {
                let value = self.require_expr(v, "value")?;
                self.check_universe_params(&level_params, &[("type", &typ), ("value", &value)])?;
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
        let name = self.require_name(v, "name")?;
        let level_params = self.name_list(v, "levelParams")?;
        let typ = self.require_expr(v, "type")?;
        self.check_quot_declaration(&kind, name, &level_params, &typ)?;
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

    /// A quotient declaration is admitted only as the constant the kernel
    /// would install itself (`add_quot` in Lean's `quot.cpp`): the right
    /// name, the right universe parameters, and exactly the kernel's type,
    /// built over the `Quot`, `Quot.mk` and `Eq` already in the environment
    /// as primitives. `try_quot` reduces `Quot.lift` and `Quot.ind` by
    /// argument position, and `Quot.ind` says every element of `Quot r` is
    /// a `Quot.mk`; both are sound only for these four constants.
    fn check_quot_declaration(
        &self,
        kind: &QuotKind,
        name: u32,
        level_params: &[u32],
        typ: &Expr,
    ) -> Result<(), TcError> {
        let (expected_name, num_levels) = match kind {
            QuotKind::Type => ("Quot", 1),
            QuotKind::Ctor => ("Quot.mk", 1),
            QuotKind::Lift => ("Quot.lift", 2),
            QuotKind::Ind => ("Quot.ind", 1),
        };
        let spelled = self.name_str(name);
        if spelled != expected_name {
            return Err(TcError::Reject(format!(
                "quotient declaration `{spelled}` is not `{expected_name}`"
            )));
        }
        if level_params.len() != num_levels
            || level_params.iter().collect::<FxHashSet<_>>().len() != num_levels
        {
            return Err(TcError::Reject(format!(
                "`{spelled}` must have {num_levels} distinct universe parameter(s)"
            )));
        }
        let eq = self.eq_primitive()?;
        let quot = match kind {
            QuotKind::Type => name,
            _ => self.quot_primitive("Quot", |k| matches!(k, QuotKind::Type))?,
        };
        let quot_mk = match kind {
            QuotKind::Ind => self.quot_primitive("Quot.mk", |k| matches!(k, QuotKind::Ctor))?,
            _ => 0,
        };
        let canonical = canonical_quot_type(kind, level_params, quot, quot_mk, eq);
        if !alpha_eq(typ, &canonical) {
            return Err(TcError::Reject(format!(
                "`{spelled}` does not have the kernel's quotient type"
            )));
        }
        Ok(())
    }

    /// The quotient primitive spelled `s`, which must already be in the
    /// environment as a quotient declaration of the right kind, not as a
    /// definition or inductive type that happens to carry the name.
    fn quot_primitive(&self, s: &str, is_kind: impl Fn(&QuotKind) -> bool) -> Result<u32, TcError> {
        match self.declared(s) {
            Some(n) => match self.env.get(n) {
                Some(ConstantInfo::Quot { kind, .. }) if is_kind(kind) => Ok(n),
                _ => Err(TcError::Reject(format!(
                    "`{s}` is not the quotient primitive the kernel installs"
                ))),
            },
            None => Err(TcError::Reject(format!(
                "quotient declaration before the primitive `{s}`"
            ))),
        }
    }

    /// `Eq` as the kernel requires it before it installs quotients
    /// (`check_eq_type`): an inductive type with one universe parameter and
    /// one constructor, of type `{α : Sort u} → α → α → Prop`, whose
    /// constructor has type `{α : Sort u} → (a : α) → @Eq.{u} α a a`.
    fn eq_primitive(&self) -> Result<u32, TcError> {
        let reject = |what: &str| TcError::Reject(format!("quotients need `Eq` {what}"));
        let Some(eq) = self.declared("Eq") else {
            return Err(reject("to be declared first"));
        };
        let Some(ConstantInfo::InductiveType { level_params, typ, ctors, .. }) = self.env.get(eq) else {
            return Err(reject("to be an inductive type"));
        };
        if level_params.len() != 1 {
            return Err(reject("with one universe parameter"));
        }
        if ctors.len() != 1 {
            return Err(reject("with one constructor"));
        }
        let u = level::param(level_params[0]);
        let sort_u = expr::sort(u.clone());
        let prop = expr::sort(level::zero());
        let eq_type = expr::pi(
            BinderInfo::Implicit,
            sort_u.clone(),
            expr::pi(
                BinderInfo::Default,
                expr::bvar(0),
                expr::pi(BinderInfo::Default, expr::bvar(1), prop),
            ),
        );
        if !alpha_eq(typ, &eq_type) {
            return Err(reject("with the type `{α : Sort u} → α → α → Prop`"));
        }
        let Some(ConstantInfo::Constructor { typ: refl_type, induct, .. }) = self.env.get(ctors[0]) else {
            return Err(reject("whose constructor is a constructor"));
        };
        let refl_expected = expr::pi(
            BinderInfo::Implicit,
            sort_u,
            expr::pi(
                BinderInfo::Default,
                expr::bvar(0),
                expr::apps(
                    expr::const_(eq, vec![u]),
                    &[expr::bvar(1), expr::bvar(0), expr::bvar(0)],
                ),
            ),
        );
        if *induct != eq || !alpha_eq(refl_type, &refl_expected) {
            return Err(reject("whose constructor has the type `{α : Sort u} → (a : α) → @Eq α a a`"));
        }
        Ok(eq)
    }

    fn handle_inductive_block(
        &mut self,
        v: &Value,
        undo: &mut InductiveUndo,
    ) -> Result<Vec<u32>, TcError> {
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

        // Name -> declared `ctors` list, for every inductive type declared
        // in *this* block. A constructor's `induct`/`cidx` are trusted
        // metadata on the constructor's own JSON object, not derived from
        // anything — without cross-checking them against the inductive's
        // own `ctors` list below, a hand-crafted export can attach an
        // arbitrary constructor (any name, any type) to an inductive that
        // does not claim it (or does not exist at all), and the checker
        // would treat it as a genuine inhabitant of whatever type its
        // `type` field says, e.g. a constructor of `False` (see
        // `orphan-ctor`: a `rogue` "constructor of `False`" whose `induct`
        // names a `Orphan` inductive that this block, and the whole file,
        // never declares).
        let mut declared_ctors: std::collections::HashMap<u32, Vec<u32>> =
            std::collections::HashMap::new();
        let mut type_names: Vec<u32> = Vec::with_capacity(types.len());
        for t in &types {
            let name = self.require_name(t, "name")?;
            self.reject_if_dup(name)?;
            type_names.push(name);
            let level_params = self.name_list(t, "levelParams")?;
            let typ = self.require_expr(t, "type")?;
            self.check_universe_params(&level_params, &[("type", &typ)])
                .map_err(|e| self.annotate(name, e))?;
            let num_params = Self::require_u32(t, "numParams")?;
            let num_indices = Self::require_u32(t, "numIndices")?;
            let all = self.name_list(t, "all")?;
            let ctor_names = self.name_list(t, "ctors")?;
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
            declared_ctors.insert(name, ctor_names.clone());
            undo.insert_constant(
                &mut self.env,
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
            let name = self.require_name(c, "name")?;
            self.reject_if_dup(name)?;
            let level_params = self.name_list(c, "levelParams")?;
            let typ = self.require_expr(c, "type")?;
            self.check_universe_params(&level_params, &[("type", &typ)])
                .map_err(|e| self.annotate(name, e))?;
            let induct = self.require_name(c, "induct")?;
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
            let Some(owner_ctors) = declared_ctors.get(&induct) else {
                return Err(TcError::Reject(format!(
                    "constructor `{}` claims inductive `{}`, which this block does not declare",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?"),
                    self.names
                        .get(induct as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            };
            if owner_ctors.get(cidx as usize) != Some(&name) {
                return Err(TcError::Reject(format!(
                    "constructor `{}` is not `{}`'s own constructor at index {cidx}",
                    self.names
                        .get(name as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?"),
                    self.names
                        .get(induct as usize)
                        .map(|s| s.as_str())
                        .unwrap_or("?")
                )));
            }
            undo.insert_constant(
                &mut self.env,
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
        struct PendingRecursor {
            name: u32,
            level_params: Vec<u32>,
            supplied_type: Expr,
            all: Vec<u32>,
            num_params: u32,
            num_indices: u32,
            num_motives: u32,
            num_minors: u32,
            k: Option<bool>,
            rules: Vec<RecRule>,
        }

        // Decode recursor records without exposing any of them through the
        // environment.  Their type, counts, `k` and rule list are assertions
        // to compare with reconstruction, never inputs to later typing.
        let mut pending_recs = Vec::with_capacity(recs.len());
        let mut pending_names = FxHashSet::default();
        for r in &recs {
            let name = self.require_name(r, "name")?;
            self.reject_if_dup(name)?;
            if !pending_names.insert(name) {
                return Err(TcError::Reject(format!(
                    "duplicate declaration of {}",
                    self.name_str(name)
                )));
            }
            let level_params = self.name_list(r, "levelParams")?;
            let typ = self.require_expr(r, "type")?;
            let all = self.name_list(r, "all")?;
            let num_params = Self::require_u32(r, "numParams")?;
            let num_indices = Self::require_u32(r, "numIndices")?;
            let num_motives = Self::require_u32(r, "numMotives")?;
            let num_minors = Self::require_u32(r, "numMinors")?;
            let is_unsafe = Self::get_bool(r, "isUnsafe");
            if is_unsafe {
                return Err(TcError::Reject(format!(
                    "unsafe recursor `{}`",
                    self.name_str(name)
                )));
            }
            let k = match r.get("k") {
                None => None,
                Some(Value::Bool(k)) => Some(*k),
                Some(_) => return Err(TcError::Reject("field `k` must be a bool".into())),
            };
            let rules = match r.get("rules") {
                None => Vec::new(),
                Some(Value::Array(arr)) => {
                    let mut out = Vec::with_capacity(arr.len());
                    for rule in arr {
                        out.push(RecRule {
                            ctor: self.require_name(rule, "ctor")?,
                            nfields: Self::require_u32(rule, "nfields")?,
                            rhs: self.require_rule_body(rule)?,
                        });
                    }
                    out
                }
                Some(_) => return Err(TcError::Reject("field `rules` must be an array".into())),
            };
            pending_recs.push(PendingRecursor {
                name,
                level_params,
                supplied_type: typ,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                k,
                rules,
            });
        }

        // Reconstruct in declaration order, followed by nested auxiliaries in
        // specialization order. Serialized signatures stay outside the
        // environment until every recursor in the block has been compared.
        // Exported `numNested` and rule RHS are not construction inputs.
        if type_names.is_empty() {
            return Err(TcError::Reject("empty inductive group".into()));
        }
        if pending_recs.is_empty() {
            return Err(TcError::Reject(
                "inductive group is missing recursors".into(),
            ));
        }
        for &name in &type_names {
            self.checker().check_inductive_group_structure(name)?;
        }
        let supplied_level_params = pending_recs[0].level_params.clone();
        let derived = self.checker().reconstruct_recursors(&type_names, &supplied_level_params)?;
        if pending_recs.len() != derived.len() {
            return Err(TcError::Reject(format!(
                "inductive group has {} recursors but reconstruction requires {}",
                pending_recs.len(),
                derived.len()
            )));
        }

        // `I.rec` is the name Lean reserves for `I`'s recursor, and it is the
        // name every user of the recursor is compiled against; the nested
        // auxiliaries are `I.rec_1`, `I.rec_2`, … after the block's first
        // type. Each reconstructed recursor is matched to the record of that
        // name, and there are as many records as reconstructed recursors, so
        // no record goes by any other name.
        let first_name = self.name_str(type_names[0]).to_string();
        let mut ordered = Vec::with_capacity(derived.len());
        for (i, d) in derived.iter().enumerate() {
            let expected_name = if i < type_names.len() {
                format!("{}.rec", self.name_str(type_names[i]))
            } else {
                format!("{first_name}.rec_{}", i - type_names.len() + 1)
            };
            let Some(pos) = pending_recs
                .iter()
                .position(|r| self.name_str(r.name) == expected_name)
            else {
                return Err(TcError::Reject(format!(
                    "inductive group is missing reconstructed recursor `{expected_name}`"
                )));
            };
            let r = pending_recs.remove(pos);
            let rname = self.name_str(r.name);
            if r.all != d.all
                || r.num_params != d.num_params
                || r.num_indices != d.num_indices
                || r.num_motives != d.num_motives
                || r.num_minors != d.num_minors
            {
                return Err(TcError::Reject(format!(
                    "recursor `{rname}` metadata does not match reconstruction"
                )));
            }
            // The rule list is the recursor's own member's constructors, in
            // their declared order, each with its field count. Iota finds a
            // recursor's constructors and, where the recursor's type cannot
            // tell two minors apart, the minor's position through this list
            // (`rec_owns_ctor`, `ctor_minor_index`), so an exported list in
            // another order selected another minor premise.
            let supplied_rules: Vec<(u32, u32)> =
                r.rules.iter().map(|rule| (rule.ctor, rule.nfields)).collect();
            if supplied_rules != d.rules {
                return Err(TcError::Reject(format!(
                    "recursor `{rname}` rules do not match its constructors"
                )));
            }
            self.checker()
                .validate_reconstructed_type(
                    &r.supplied_type,
                    &r.level_params,
                    &d.typ,
                    &d.level_params,
                )
                .map_err(|e| match e {
                    TcError::Reject(_) => {
                        TcError::Reject(format!(
                            "recursor `{rname}` type does not match reconstructed type"
                        ))
                    }
                    TcError::Decline(msg) => TcError::Decline(format!(
                        "recursor `{rname}` type reconstruction: {msg}"
                    )),
                    TcError::Other(msg) => TcError::Other(format!(
                        "recursor `{rname}` type reconstruction: {msg}"
                    )),
                })?;
            // K-like reduction is decided from the declaration, here and at
            // every use; a supplied flag has to agree with it.
            if let Some(k) = r.k {
                if k != d.k {
                    return Err(TcError::Reject(format!(
                        "recursor `{rname}` has k={k} but reconstruction gives k={}",
                        d.k
                    )));
                }
            }
            // Store the reconstructed type under this declaration's own
            // validated alpha labels.  No serialized type structure crosses
            // the transaction boundary.
            let levels: Vec<Level> = r.level_params.iter().copied().map(level::param).collect();
            let subst = level::subst_map(&d.level_params, &levels);
            let mut stored = d.clone();
            stored.typ = expr::instantiate_level_params(&d.typ, &subst);
            stored.level_params = r.level_params.clone();
            ordered.push((r, stored));
        }
        // Ownership and the group's minor order follow reconstruction, not
        // the records: the i-th declared type is eliminated by the i-th
        // reconstructed recursor, and the minors of every recursor in the
        // block are the members' constructors in member order, which is the
        // order of `ordered` (Lean's `rec_k`).
        let group: Vec<u32> = ordered.iter().map(|(r, _)| r.name).collect();
        for (i, (r, d)) in ordered.into_iter().enumerate() {
            if let Some(owner) = type_names.get(i) {
                undo.insert_owner(&mut self.env, *owner, r.name);
            }
            undo.insert_constant(
                &mut self.env,
                r.name,
                ConstantInfo::Recursor {
                    level_params: d.level_params,
                    typ: d.typ,
                    all: d.all,
                    num_params: d.num_params,
                    num_indices: d.num_indices,
                    num_motives: d.num_motives,
                    num_minors: d.num_minors,
                    rules: r.rules,
                    k: d.k,
                    is_unsafe: false,
                },
            );
        }
        for n in &group {
            undo.insert_group(&mut self.env, *n, group.clone());
        }
        Ok(type_names)
    }

    /// Nested specializations actually occurring in constructor fields of
    /// `type_names`, including those found by instantiating a previous
    /// inductive's constructors (Array T also yields List T).
    fn counted_nested(&self, type_names: &[u32]) -> usize {
        let mut seen: FxHashSet<Expr> = FxHashSet::default();
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
        seen: &mut FxHashSet<Expr>,
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
        seen: &mut FxHashSet<Expr>,
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
            // Keyed by the expression's own *structural* `Hash`/`Eq`
            // (`ExprData` derives both, and `Rc<T>`'s in turn delegate to
            // `T`'s), not by `Rc::as_ptr`: `expr::apps`/`expr::const_` both
            // go through the global intern table, which already
            // deduplicates by structural hash — `Const`'s own `us: Rc<Vec
            // <Level>>` field hashes/compares structurally too, so
            // `us.to_vec()` reallocating a fresh `Vec` each call is not
            // itself the problem. The pointer was still unstable because
            // `ctor_field_tys` (below) fed this call subtly different
            // *values* for `params` on repeat visits to the same nested
            // specialization (see its own doc comment), not merely
            // different pointers to the same value; fixing that is what
            // makes this structural key actually converge.
            let key_e = expr::apps(expr::const_(m, us.to_vec()), params);
            if !seen.insert(key_e) {
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
    /// Check an export file: a first pass over the file computes when each
    /// expression node can be released (`lifetime`), then the export is
    /// checked line by line, releasing nodes as they expire.
    pub fn run_file(&mut self, path: &str) -> Result<(), TcError> {
        if std::env::var_os("KIOTA_KEEP_EXPORT_NODES").is_none() {
            let lt = crate::lifetime::scan(path).map_err(|e| TcError::Other(format!("io: {e}")))?;
            if std::env::var_os("KIOTA_PROGRESS").is_some() {
                eprintln!("LIFETIMES lines={} nodes={} long_lived={}", lt.lines, lt.nodes, lt.long_lived());
            }
            self.lifetimes = Some(lt);
        }
        if std::env::var_os("KIOTA_KEEP_THEOREM_VALUES").is_none()
            && std::env::var_os("KIOTA_NO_PROOF_STORE").is_none()
        {
            self.proofs = Some(crate::proofstore::ProofStore::new());
        }
        let file = std::fs::File::open(path).map_err(|e| TcError::Other(format!("io: {e}")))?;
        let r = self.run(std::io::BufReader::with_capacity(1 << 22, file));
        if std::env::var_os("KIOTA_PROGRESS").is_some() {
            eprintln!(
                "NAMES names={} second_indices={} table={}",
                self.name_by_str.len(),
                self.aliased_names,
                self.name_canon.len()
            );
            if let Some(store) = self.proofs.as_ref() {
                eprintln!(
                    "PROOFSTORE theorems={} bytes={} loads={}",
                    store.stored(),
                    store.bytes(),
                    store.loads()
                );
            }
        }
        r
    }

    pub fn run<R: BufRead>(&mut self, reader: R) -> Result<(), TcError> {
        for line in reader.lines() {
            let line = line.map_err(|e| TcError::Other(format!("io: {e}")))?;
            self.line_no += 1;
            if line.trim().is_empty() {
                continue;
            }
            let v: Value = serde_json::from_str(&line)
                .map_err(|e| TcError::Other(format!("json parse: {e} on line: {line}")))?;
            let result = self.handle_line(&v);
            // Release after every declaration line, failed or not: in
            // diagnostic modes the run continues past a failure.
            if !matches!(result, Ok(false)) {
                self.release_expired();
            }
            result?;
        }
        Ok(())
    }

    /// Drop the table slots of every node whose last reference is behind the
    /// current line. The environment keeps what it still needs.
    fn release_expired(&mut self) {
        let Parser { lifetimes, exprs, line_no, .. } = self;
        if let Some(lt) = lifetimes.as_mut() {
            lt.release_after_decl(*line_no, exprs.len() as u32, |idx| exprs[idx as usize] = None);
        }
    }

    /// Once a theorem is checked its proof is only read again by
    /// `unfold_delta`. With a proof store (file input) every proof goes to
    /// disk and is released from memory; the checker reads it back when a
    /// comparison unfolds the theorem. If the store cannot be written the
    /// proofs stay in memory from then on, which is always sound.
    ///
    /// Without a store: a theorem's proof is unfolded only through a
    /// `const` node naming the theorem, which the pre-pass has seen if the
    /// export has one. Once a theorem no expression refers to is checked,
    /// its proof is released; a referenced theorem keeps its proof whatever
    /// its size, so no unfolding Lean would do is lost. `unfold_delta`
    /// declines if a released proof is ever needed, which only a pre-pass
    /// gap could cause. `KIOTA_KEEP_THEOREM_VALUES` keeps every proof.
    fn release_theorem_value(&mut self, name: u32) {
        if std::env::var_os("KIOTA_KEEP_THEOREM_VALUES").is_some() {
            return;
        }
        if let Some(store) = self.proofs.as_ref() {
            let stored = match self.env.consts.get(&name) {
                Some(ConstantInfo::Theorem { value: Some(v), .. }) => store.store(name, v),
                _ => return,
            };
            match stored {
                Ok(()) => {
                    if let Some(ConstantInfo::Theorem { value, .. }) = self.env.consts.get_mut(&name) {
                        *value = None;
                    }
                }
                Err(e) => {
                    eprintln!("PROOFSTORE write failed ({e}); keeping theorem proofs in memory");
                    self.proofs = None;
                }
            }
            return;
        }
        let Some(lt) = self.lifetimes.as_ref() else { return };
        // The pre-pass knows which name indices the expressions mention, and
        // an index is the name only while no name has a second index.
        if self.aliased_names > 0 || lt.name_referenced(name) {
            return;
        }
        if let Some(ConstantInfo::Theorem { value, .. }) = self.env.consts.get_mut(&name) {
            *value = None;
        }
    }

    /// `Ok(true)` for a declaration record (one kernel transaction), `Ok(false)`
    /// for names, levels, expressions and metadata.
    ///
    /// A line is one record of one kind, as in lean4export's own reader: a
    /// table entry is its index key and its payload, a declaration is its
    /// one key. Anything else is rejected, not skipped: a record this reader
    /// does not know could be a declaration it then never checks.
    fn handle_line(&mut self, v: &Value) -> Result<bool, TcError> {
        let Some(obj) = v.as_object() else {
            return Err(TcError::Reject("export line is not a JSON object".into()));
        };
        // A table entry without its payload is left to its handler, which
        // says what is missing.
        let table = obj.contains_key("in") || obj.contains_key("il") || obj.contains_key("ie");
        if obj.len() > if table { 2 } else { 1 } {
            let keys: Vec<&str> = obj.keys().map(|k| k.as_str()).collect();
            return Err(TcError::Reject(format!(
                "export record with keys {keys:?} is not one record"
            )));
        }
        if obj.contains_key("meta") {
            return Ok(false);
        }
        if obj.contains_key("in") {
            self.handle_name(v)?;
            return Ok(false);
        }
        if obj.contains_key("il") {
            self.handle_level(v)?;
            return Ok(false);
        }
        if obj.contains_key("ie") {
            self.handle_expr(v)?;
            return Ok(false);
        }
        if let Some(d) = v.get("axiom") {
            self.handle_def_like("axiomDecl", d).map_err(|e| self.annotate_record(d, e))?;
            self.check_last(d, "axiom")?;
            return Ok(true);
        }
        if let Some(d) = v.get("def") {
            self.handle_def_like("defnDecl", d).map_err(|e| self.annotate_record(d, e))?;
            self.check_last(d, "def")?;
            return Ok(true);
        }
        if let Some(d) = v.get("thm") {
            self.handle_def_like("thmDecl", d).map_err(|e| self.annotate_record(d, e))?;
            self.check_last(d, "theorem")?;
            return Ok(true);
        }
        if let Some(d) = v.get("opaque") {
            self.handle_def_like("opaqueDecl", d).map_err(|e| self.annotate_record(d, e))?;
            self.check_last(d, "opaque")?;
            return Ok(true);
        }
        if let Some(d) = v.get("quot") {
            self.handle_quot(d).map_err(|e| self.annotate_record(d, e))?;
            return Ok(true);
        }
        if let Some(d) = v.get("inductive") {
            // An inductive block is one kernel transaction.  In particular,
            // a malformed supplied recursor type must not leave the block's
            // types, constructors, recursors, or ownership maps visible to a
            // later declaration in the stream.
            let mut undo = InductiveUndo::default();
            let result = (|| {
                let names = self.handle_inductive_block(d, &mut undo)?;
                for n in names {
                    self.checker()
                        .check_inductive_group(n)
                        .map_err(|e| self.annotate(n, e))?;
                }
                Ok(())
            })();
            if result.is_err() {
                undo.rollback(&mut self.env);
            }
            return result.map(|()| true);
        }
        let keys: Vec<&str> = obj.keys().map(|k| k.as_str()).collect();
        Err(TcError::Reject(format!("unknown export record with keys {keys:?}")))
    }

    fn check_last(&mut self, d: &Value, kind: &str) -> Result<(), TcError> {
        let name = self.require_name(d, "name")?;
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
        self.checker()
            .check_decl(name, kind)
            .map_err(|e| self.annotate(name, e))?;
        self.release_theorem_value(name);
        Ok(())
    }

    /// `annotate` with the record's own `name`, for errors raised while a
    /// declaration is read, before `check_decl` sees it.
    fn annotate_record(&self, d: &Value, e: TcError) -> TcError {
        match d.get("name").and_then(|x| x.as_u64()).map(|n| self.name_canon.get(n as usize)) {
            Some(Some(&c)) if c != NO_NAME => self.annotate(c, e),
            _ => e,
        }
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



/// Structural equality up to binder annotations. Binder names are not in
/// `ExprData`; binder infos are, and the kernel's `expr` equality ignores
/// them, so the canonical quotient types compare without them too.
fn alpha_eq(a: &Expr, b: &Expr) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    match (&***a, &***b) {
        (ExprData::BVar(i), ExprData::BVar(j)) => i == j,
        (ExprData::Sort(l1), ExprData::Sort(l2)) => l1 == l2,
        (ExprData::Const(n1, us1), ExprData::Const(n2, us2)) => n1 == n2 && us1 == us2,
        (ExprData::App(f1, a1), ExprData::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (ExprData::Lam(_, t1, b1), ExprData::Lam(_, t2, b2))
        | (ExprData::Pi(_, t1, b1), ExprData::Pi(_, t2, b2)) => alpha_eq(t1, t2) && alpha_eq(b1, b2),
        (ExprData::Let(t1, v1, b1), ExprData::Let(t2, v2, b2)) => {
            alpha_eq(t1, t2) && alpha_eq(v1, v2) && alpha_eq(b1, b2)
        }
        (ExprData::Proj(s1, i1, e1), ExprData::Proj(s2, i2, e2)) => {
            s1 == s2 && i1 == i2 && alpha_eq(e1, e2)
        }
        (ExprData::Lit(l1), ExprData::Lit(l2)) => l1 == l2,
        _ => false,
    }
}

/// The kernel's quotient declarations as `add_quot` builds them (Lean 4
/// `src/kernel/quot.cpp`), in de Bruijn form over the given `Quot`,
/// `Quot.mk` and `Eq` name indices and the declared universe parameters:
///
/// ```text
/// Quot.{u}        : {α : Sort u} → (r : α → α → Prop) → Sort u
/// Quot.mk.{u}     : {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot.{u} α r
/// Quot.lift.{u v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
///                   → (∀ (a b : α), r a b → @Eq.{v} β (f a) (f b)) → @Quot.{u} α r → β
/// Quot.ind.{u}    : {α : Sort u} → {r : α → α → Prop} → {β : @Quot.{u} α r → Prop}
///                   → (∀ (a : α), β (@Quot.mk.{u} α r a)) → ∀ (q : @Quot.{u} α r), β q
/// ```
fn canonical_quot_type(kind: &QuotKind, level_params: &[u32], quot: u32, quot_mk: u32, eq: u32) -> Expr {
    use BinderInfo::{Default, Implicit};
    let u = level::param(level_params[0]);
    let sort_u = expr::sort(u.clone());
    let prop = expr::sort(level::zero());
    let bv = expr::bvar;
    // `α → α → Prop` with `α` at index `a` (so `a + 1` under the first arrow).
    let rel = |a: u32| expr::pi(Default, bv(a), expr::pi(Default, bv(a + 1), prop.clone()));
    // `@Quot.{u} α r`
    let quot_app = |a: u32, r: u32| expr::apps(expr::const_(quot, vec![u.clone()]), &[bv(a), bv(r)]);
    match kind {
        // {α} (r)
        QuotKind::Type => expr::pi(Implicit, sort_u.clone(), expr::pi(Default, rel(0), sort_u)),
        // {α} (r) (a) ↦ Quot α r
        QuotKind::Ctor => expr::pi(
            Implicit,
            sort_u,
            expr::pi(Default, rel(0), expr::pi(Default, bv(1), quot_app(2, 1))),
        ),
        QuotKind::Lift => {
            let v = level::param(level_params[1]);
            let sort_v = expr::sort(v.clone());
            // Under {α} {r} {β} (f): f=#0 β=#1 r=#2 α=#3.
            // ∀ (a b : α), r a b → @Eq.{v} β (f a) (f b)
            let sanity = expr::pi(
                Default,
                bv(3),
                expr::pi(
                    Default,
                    bv(4),
                    expr::pi(
                        Default,
                        expr::apps(bv(4), &[bv(1), bv(0)]),
                        expr::apps(
                            expr::const_(eq, vec![v]),
                            &[bv(4), expr::app(bv(3), bv(2)), expr::app(bv(3), bv(1))],
                        ),
                    ),
                ),
            );
            expr::pi(
                Implicit,
                sort_u,
                expr::pi(
                    Implicit,
                    rel(0),
                    expr::pi(
                        Implicit,
                        sort_v,
                        expr::pi(
                            Default,
                            expr::pi(Default, bv(2), bv(1)),
                            expr::pi(Default, sanity, expr::pi(Default, quot_app(4, 3), bv(3))),
                        ),
                    ),
                ),
            )
        }
        QuotKind::Ind => {
            // Under {α} {r} {β}: β=#0 r=#1 α=#2; under a further (a : α): a=#0 β=#1 r=#2 α=#3.
            let mk = expr::pi(
                Default,
                bv(2),
                expr::app(
                    bv(1),
                    expr::apps(expr::const_(quot_mk, vec![u.clone()]), &[bv(3), bv(2), bv(0)]),
                ),
            );
            expr::pi(
                Implicit,
                sort_u,
                expr::pi(
                    Implicit,
                    rel(0),
                    expr::pi(
                        Implicit,
                        expr::pi(Default, quot_app(1, 0), prop.clone()),
                        expr::pi(
                            Default,
                            mk,
                            expr::pi(Default, quot_app(3, 2), expr::app(bv(2), bv(0))),
                        ),
                    ),
                ),
            )
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
    // Each successive field's domain lives one binder deeper than the
    // last (`Pi(f0, Pi(f1, Pi(f2, ...)))`): a free variable referring to
    // something *outside* this constructor's own telescope (e.g. the
    // already-substituted outer params from `inst` above) sits at index
    // `k` higher in the `k`-th field than in the first. Returning
    // `dom.clone()` as-is silently left every field at its own,
    // uncorrected depth. Callers that treat every entry of the returned
    // `Vec` as living at the same (depth-0) frame of reference —
    // `note_nested_app` does exactly this, scanning each field for
    // occurrences of an outer group's own names and reusing the result as
    // `params` for the *next* recursion level — then saw the outer
    // params' bvar index drift upward by one per field position, and by
    // one more with every additional nesting level recursed into. That is
    // a genuine change in *value*, not just a fresh, unstable pointer to
    // an unchanged value, so no amount of re-keying `note_nested_app`'s
    // own dedup set fixes it on its own: each "repeat" visit to the same
    // logical nested specialization (e.g. `Lean.PersistentHashMap.Node`'s
    // `Array (Entry .. (Node ..))` cycling back through `List`/`Entry`)
    // was really a *different* term one bvar index further out, so it
    // never converged — turning what should be a small, finite BFS into
    // one that never terminates. Shifting each field's domain down by its
    // own position renormalizes it back to the same frame of reference as
    // field 0; the shift's cutoff leaves any (rare) reference to a
    // *sibling* field itself (index below the field's own position)
    // untouched.
    let mut fields = Vec::new();
    let mut k: u32 = 0;
    loop {
        match &**cur {
            ExprData::Pi(_, dom, body) => {
                fields.push(expr::shift(dom, -(k as i32), k));
                cur = body.clone();
                k += 1;
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
