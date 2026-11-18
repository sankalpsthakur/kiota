use crate::expr::Expr;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone)]
pub struct RecRule {
    pub ctor: u32,
    pub nfields: u32,
    pub rhs: Expr,
}

#[derive(Debug, Clone)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug, Clone)]
pub enum ConstantInfo {
    Axiom {
        level_params: Vec<u32>,
        typ: Expr,
        is_unsafe: bool,
    },
    Def {
        level_params: Vec<u32>,
        typ: Expr,
        value: Expr,
        hints: ReducibilityHints,
        is_unsafe: bool,
    },
    Theorem {
        level_params: Vec<u32>,
        typ: Expr,
        /// `None` once the parser has checked a theorem that no expression
        /// in the export refers to and released its proof. An unfold that
        /// would need a released proof declines; see
        /// `Parser::release_theorem_value`.
        value: Option<Expr>,
    },
    Opaque {
        level_params: Vec<u32>,
        typ: Expr,
        value: Expr,
        is_unsafe: bool,
    },
    Quot {
        kind: QuotKind,
        level_params: Vec<u32>,
        typ: Expr,
    },
    InductiveType {
        level_params: Vec<u32>,
        typ: Expr,
        num_params: u32,
        num_indices: u32,
        all: Vec<u32>,
        ctors: Vec<u32>,
        is_rec: bool,
        is_unsafe: bool,
    },
    Constructor {
        level_params: Vec<u32>,
        typ: Expr,
        induct: u32,
        cidx: u32,
        num_params: u32,
        num_fields: u32,
        is_unsafe: bool,
    },
    Recursor {
        level_params: Vec<u32>,
        typ: Expr,
        all: Vec<u32>,
        num_params: u32,
        num_indices: u32,
        num_motives: u32,
        num_minors: u32,
        rules: Vec<RecRule>,
        k: bool,
        is_unsafe: bool,
    },
}

impl ConstantInfo {
    pub fn level_params(&self) -> &[u32] {
        match self {
            ConstantInfo::Axiom { level_params, .. }
            | ConstantInfo::Def { level_params, .. }
            | ConstantInfo::Theorem { level_params, .. }
            | ConstantInfo::Opaque { level_params, .. }
            | ConstantInfo::Quot { level_params, .. }
            | ConstantInfo::InductiveType { level_params, .. }
            | ConstantInfo::Constructor { level_params, .. }
            | ConstantInfo::Recursor { level_params, .. } => level_params,
        }
    }
    pub fn typ(&self) -> &Expr {
        match self {
            ConstantInfo::Axiom { typ, .. }
            | ConstantInfo::Def { typ, .. }
            | ConstantInfo::Theorem { typ, .. }
            | ConstantInfo::Opaque { typ, .. }
            | ConstantInfo::Quot { typ, .. }
            | ConstantInfo::InductiveType { typ, .. }
            | ConstantInfo::Constructor { typ, .. }
            | ConstantInfo::Recursor { typ, .. } => typ,
        }
    }
    pub fn value(&self) -> Option<&Expr> {
        match self {
            ConstantInfo::Def { value, .. } | ConstantInfo::Opaque { value, .. } => Some(value),
            ConstantInfo::Theorem { value, .. } => value.as_ref(),
            _ => None,
        }
    }
    pub fn is_unsafe(&self) -> bool {
        match self {
            ConstantInfo::Axiom { is_unsafe, .. }
            | ConstantInfo::Def { is_unsafe, .. }
            | ConstantInfo::Opaque { is_unsafe, .. }
            | ConstantInfo::InductiveType { is_unsafe, .. }
            | ConstantInfo::Constructor { is_unsafe, .. }
            | ConstantInfo::Recursor { is_unsafe, .. } => *is_unsafe,
            ConstantInfo::Theorem { .. } | ConstantInfo::Quot { .. } => false,
        }
    }
}

/// Source of `Environment::epoch` values, shared by every thread so that two
/// environments never carry the same one.
static NEXT_EPOCH: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

fn fresh_epoch() -> u64 {
    NEXT_EPOCH.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

pub struct Environment {
    pub consts: FxHashMap<u32, ConstantInfo>,
    /// Inductive type name → recursor name, filled in by the parser.
    pub rec_of: FxHashMap<u32, u32>,
    /// Recursor → every recursor in its inductive block (`.rec`, `.rec_1`, …),
    /// sorted so main comes first. Used for nested ι, not for trusting RHS.
    pub rec_group: FxHashMap<u32, Vec<u32>>,
    /// Identifies this environment and the history of its constants as far
    /// as a cache of facts about closed terms cares: it stays the same for
    /// as long as constants are only added. Replacing or removing one
    /// (`insert` over an existing name, `invalidate` after a rollback)
    /// takes a fresh value. The cross-declaration caches in `tc` are keyed
    /// by node identity alone, and a name index is another constant in
    /// another environment, so they are emptied whenever the epoch they
    /// were filled under is not the one being checked against.
    epoch: u64,
}

impl Default for Environment {
    fn default() -> Self {
        Environment {
            consts: FxHashMap::default(),
            rec_of: FxHashMap::default(),
            rec_group: FxHashMap::default(),
            epoch: fresh_epoch(),
        }
    }
}

impl Environment {
    pub fn get(&self, n: u32) -> Option<&ConstantInfo> {
        self.consts.get(&n)
    }
    pub fn insert(&mut self, n: u32, ci: ConstantInfo) {
        if self.consts.insert(n, ci).is_some() {
            self.invalidate();
        }
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    /// Call after a constant was replaced or taken out again: facts cached
    /// about the old constants must not be read back.
    pub fn invalidate(&mut self) {
        self.epoch = fresh_epoch();
    }
}
