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

/// A reduction the checker performs natively instead of by unfolding the
/// constant's definition. Each is tied to one declared constant, and only
/// once that declaration has been validated (`tc::extensions`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtOp {
    NatAdd,
    NatSub,
    NatMul,
    NatPow,
    NatDiv,
    NatMod,
    NatGcd,
    NatBeq,
    NatBle,
    NatLand,
    NatLor,
    NatXor,
    NatShiftLeft,
    NatShiftRight,
    Decide,
    Ite,
    Dite,
}

impl ExtOp {
    pub const ALL: [ExtOp; 17] = [
        ExtOp::NatAdd,
        ExtOp::NatSub,
        ExtOp::NatMul,
        ExtOp::NatPow,
        ExtOp::NatDiv,
        ExtOp::NatMod,
        ExtOp::NatGcd,
        ExtOp::NatBeq,
        ExtOp::NatBle,
        ExtOp::NatLand,
        ExtOp::NatLor,
        ExtOp::NatXor,
        ExtOp::NatShiftLeft,
        ExtOp::NatShiftRight,
        ExtOp::Decide,
        ExtOp::Ite,
        ExtOp::Dite,
    ];

    /// The name Lean gives the constant the reduction belongs to.
    pub fn spelling(self) -> &'static str {
        match self {
            ExtOp::NatAdd => "Nat.add",
            ExtOp::NatSub => "Nat.sub",
            ExtOp::NatMul => "Nat.mul",
            ExtOp::NatPow => "Nat.pow",
            ExtOp::NatDiv => "Nat.div",
            ExtOp::NatMod => "Nat.mod",
            ExtOp::NatGcd => "Nat.gcd",
            ExtOp::NatBeq => "Nat.beq",
            ExtOp::NatBle => "Nat.ble",
            ExtOp::NatLand => "Nat.land",
            ExtOp::NatLor => "Nat.lor",
            ExtOp::NatXor => "Nat.xor",
            ExtOp::NatShiftLeft => "Nat.shiftLeft",
            ExtOp::NatShiftRight => "Nat.shiftRight",
            ExtOp::Decide => "Decidable.decide",
            ExtOp::Ite => "ite",
            ExtOp::Dite => "dite",
        }
    }

    pub fn from_spelling(s: &str) -> Option<ExtOp> {
        ExtOp::ALL.iter().copied().find(|op| op.spelling() == s)
    }
}

/// The constants the checker treats specially, by declaration index. A
/// field is set only after the declaration it names has been validated
/// against what the reduction assumes of it; until then, and for good if
/// the validation fails, the constant is an ordinary one. Nothing in the
/// checker asks what a constant is called.
#[derive(Debug, Clone, Copy, Default)]
pub struct Extensions {
    /// The type of `Nat` literals.
    pub nat: Option<u32>,
    /// `Nat.zero` and `Nat.succ`: what a literal is made of.
    pub nat_ctors: Option<(u32, u32)>,
    /// A constant named `Nat` is declared and is not Lean's `Nat`.
    pub nat_forged: bool,
    pub bool_false: Option<u32>,
    pub bool_true: Option<u32>,
    pub decidable_is_false: Option<u32>,
    pub decidable_is_true: Option<u32>,
    /// `Nat.pred`, the right-hand side of the `Nat.sub` rule.
    pub nat_pred: Option<u32>,
    /// `Nat.bitwise`, which `Nat.land`, `Nat.lor` and `Nat.xor` are stated with.
    pub nat_bitwise: Option<u32>,
    /// The type of `String` literals: the structure `String`, once
    /// `String.ofList` has been validated, so that a literal denotes a term.
    pub string: Option<u32>,
    /// A constant named `String` is declared and cannot be the literals' type.
    pub string_forged: bool,
    /// The structure named `String`, from its declaration on.
    pub string_candidate: Option<u32>,
    /// `Char.ofNat : Nat → Char` and that `Char`.
    pub char_of_nat: Option<u32>,
    pub char_ty: Option<u32>,
    /// `String.ofList : List Char → String` and that `List`'s constructors:
    /// the literal `"ab"` is `String.ofList [Char.ofNat 97, Char.ofNat 98]`.
    pub string_of_list: Option<u32>,
    pub list_nil: Option<u32>,
    pub list_cons: Option<u32>,
    op_ids: [u32; ExtOp::ALL.len()],
    op_kinds: [Option<ExtOp>; ExtOp::ALL.len()],
    op_len: u8,
}

impl Extensions {
    /// The native reduction, if any, enabled for the constant `n`.
    #[inline]
    pub fn op_of(&self, n: u32) -> Option<ExtOp> {
        let len = self.op_len as usize;
        let mut i = 0;
        while i < len {
            if self.op_ids[i] == n {
                return self.op_kinds[i];
            }
            i += 1;
        }
        None
    }

    /// The constant `op` is enabled for.
    pub fn id_of(&self, op: ExtOp) -> Option<u32> {
        (0..self.op_len as usize)
            .find(|i| self.op_kinds[*i] == Some(op))
            .map(|i| self.op_ids[i])
    }

    pub fn enable(&mut self, op: ExtOp, n: u32) {
        if self.id_of(op).is_some() {
            return;
        }
        let i = self.op_len as usize;
        self.op_ids[i] = n;
        self.op_kinds[i] = Some(op);
        self.op_len += 1;
    }
}

#[derive(Default)]
pub struct Environment {
    /// Validated extension constants; see `Extensions`.
    pub ext: Extensions,
    /// The native reduct of a string literal's bytes has been compared with
    /// `String.ofList`'s (`Checker::native_string_projection_ok`). Set once;
    /// an environment only grows, so the comparison stays true.
    pub native_string_values_ok: std::cell::Cell<bool>,
    pub consts: FxHashMap<u32, ConstantInfo>,
    /// Inductive type name → recursor name, filled in by the parser.
    pub rec_of: FxHashMap<u32, u32>,
    /// Recursor → every recursor in its inductive block (`.rec`, `.rec_1`, …),
    /// sorted so main comes first. Used for nested ι, not for trusting RHS.
    pub rec_group: FxHashMap<u32, Vec<u32>>,
}

impl Environment {
    pub fn get(&self, n: u32) -> Option<&ConstantInfo> {
        self.consts.get(&n)
    }
    pub fn insert(&mut self, n: u32, ci: ConstantInfo) {
        self.consts.insert(n, ci);
    }
}
