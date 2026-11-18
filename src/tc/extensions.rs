//! The constants the checker reduces natively, and what each must be before
//! it does.
//!
//! Lean's kernel computes `Nat.add 2 3` with GMP because the constant is
//! *named* `Nat.add`; it never looks at the definition. An export is free to
//! declare `def Nat.add (a b : Nat) : Nat := b`, and then the native rule and
//! the definition disagree: `Nat.add 2 2` is `4` by the first and `2` by the
//! second, and `False` follows. This checker has more such rules than the
//! kernel (`ite`, `dite` and `Decidable.decide` at a constructor instance),
//! so the same holds for them.
//!
//! Here a rule is tied to a declaration, not to a name. When a constant with
//! one of the names below is *declared*, `on_declared` checks that it is what
//! the rule assumes, and only then enters it in `Extensions`. A constant that
//! fails is not rejected: it is an ordinary constant that reduces by its own
//! definition, which is always sound.
//!
//! What is checked, in the manner of lean4lean's `Primitive.lean`:
//!
//! * `Nat`, `Bool`, `Decidable`: the inductive type itself, constructor by
//!   constructor, in Lean's order.
//! * `Nat.add`, `Nat.pred`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`,
//!   `Nat.ble`, `Nat.shiftLeft`, `Nat.shiftRight`: a definition without
//!   universe parameters, of the right type, whose defining equations hold by
//!   ordinary reduction on variables, e.g. `Nat.add x 0 ≡ x` and
//!   `Nat.add x (succ y) ≡ succ (Nat.add x y)`. Those equations determine the
//!   function on numerals, which is what the native rule computes, and they
//!   are the symbolic rules `try_nat_extension` applies to open terms. An
//!   equation that mentions another operation (`Nat.mul` is stated with
//!   `Nat.add`) needs that one validated first.
//! * `ite`, `dite`, `Decidable.decide`: both rules, at both constructors of
//!   the validated `Decidable`, on variables.
//! * `Nat.land`, `Nat.lor`, `Nat.xor`: `Nat.bitwise f` for an `f` with the
//!   right truth table.
//! * `Nat.div`, `Nat.mod`, `Nat.modCore`, `Nat.gcd`, `Nat.bitwise`: a
//!   definition of the right type and no more. Their recursions are by fuel
//!   or well-founded, and the equations that pin them down (lean4lean's
//!   `checkNatFuelRec`, `unfoldNatWellFounded`) are not ported. For these the
//!   checker trusts the name exactly as Lean's kernel does.
//!
//! The equations are checked with the extension under validation still off,
//! so they are statements about the declared definition and nothing else.

use super::*;

/// Run `f` with the statistics counters paused: validation is not part of
/// checking any declaration, and the counters are compared across builds.
fn uncounted<T>(f: impl FnOnce() -> T) -> T {
    let was = crate::stats::pause(true);
    let r = f();
    crate::stats::pause(was);
    r
}

fn trace_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("KIOTA_EXT_TRACE").is_some())
}

/// The names `on_declared` acts on.
fn is_extension_spelling(s: &str) -> bool {
    matches!(s, "Nat" | "Bool" | "Decidable" | "String" | "Nat.pred" | "Nat.bitwise")
        || ExtOp::from_spelling(s).is_some()
}

/// The parser calls this once a declaration has been admitted and checked.
/// If `name` is spelled like an extension constant it is validated, and the
/// table to use from here on is returned when it changed. A constant that
/// fails stays out of the table; the reason goes to stderr, since a genuine
/// export never produces one.
pub fn on_declared(
    env: &Environment,
    names: &[Rc<String>],
    proofs: Option<&crate::proofstore::ProofStore>,
    name: u32,
) -> Option<Extensions> {
    let spelled = names.get(name as usize).map(|s| s.as_str()).unwrap_or("");
    // Every extension name starts with one of these letters; nearly every
    // declaration is turned away here.
    if !matches!(spelled.as_bytes().first(), Some(b'N' | b'B' | b'D' | b'S' | b'i' | b'd')) {
        return None;
    }
    if !is_extension_spelling(spelled) {
        return None;
    }
    let v = Validator { env, names, proofs, ext: env.ext };
    let mut ext = env.ext;
    match uncounted(|| v.validate(name, spelled, &mut ext)) {
        Ok(()) => {
            if trace_enabled() {
                eprintln!("EXT on {spelled}");
            }
            Some(ext)
        }
        Err(why) => {
            eprintln!("kiota: `{spelled}` is not the constant the kernel assumes ({why}); it gets no native reduction");
            match spelled {
                "Nat" => ext.nat_forged = true,
                "String" => ext.string_forged = true,
                _ => return None,
            }
            Some(ext)
        }
    }
}

struct Validator<'a> {
    env: &'a Environment,
    names: &'a [Rc<String>],
    proofs: Option<&'a crate::proofstore::ProofStore>,
    /// The table as it stands, without the constant under validation.
    ext: Extensions,
}

type V = Result<(), String>;

fn no(why: impl Into<String>) -> V {
    Err(why.into())
}

fn c(n: u32) -> Expr {
    expr::const_(n, vec![])
}

fn arrow(a: Expr, b: Expr) -> Expr {
    // Used with closed `a` and `b` only.
    expr::pi(BinderInfo::Default, a, b)
}

/// `fun (x₁ : tys[0]) … (xₙ : tys[n-1]) => body`; each type is stated under
/// the binders before it.
fn lams(tys: &[Expr], body: Expr) -> Expr {
    tys.iter().rev().fold(body, |b, t| expr::lam(BinderInfo::Default, t.clone(), b))
}

fn is_const(e: &Expr, n: u32) -> bool {
    matches!(&***e, ExprData::Const(m, us) if *m == n && us.is_empty())
}

fn is_sort(e: &Expr, l: &Level) -> bool {
    matches!(&***e, ExprData::Sort(s) if level::is_def_eq(s, l))
}

impl Validator<'_> {
    fn spelled(&self, n: u32) -> &str {
        self.names.get(n as usize).map(|s| s.as_str()).unwrap_or("")
    }

    fn validate(&self, name: u32, spelled: &str, ext: &mut Extensions) -> V {
        match spelled {
            "Nat" => {
                let (zero, succ) = self.validate_nat(name)?;
                ext.nat = Some(name);
                ext.nat_ctors = Some((zero, succ));
                Ok(())
            }
            "Bool" => {
                let (f, t) = self.validate_bool(name)?;
                ext.bool_false = Some(f);
                ext.bool_true = Some(t);
                Ok(())
            }
            "Decidable" => {
                let (f, t, _) = self.validate_decidable(name)?;
                ext.decidable_is_false = Some(f);
                ext.decidable_is_true = Some(t);
                Ok(())
            }
            "String" => {
                self.validate_string(name)?;
                ext.string = Some(name);
                Ok(())
            }
            "Nat.pred" => {
                self.validate_nat_pred(name)?;
                ext.nat_pred = Some(name);
                Ok(())
            }
            "Nat.bitwise" => {
                self.validate_nat_bitwise(name)?;
                ext.nat_bitwise = Some(name);
                Ok(())
            }
            _ => {
                let op = ExtOp::from_spelling(spelled).ok_or("not an extension")?;
                self.validate_op(op, name)?;
                ext.enable(op, name);
                Ok(())
            }
        }
    }

    // ---------------- inductive types ----------------

    /// `inductive Nat : Type | zero : Nat | succ : Nat → Nat`, the
    /// constructors under those names and in that order: a literal `n` is
    /// `succ^n zero`, and ι on a literal picks its rule by position.
    fn validate_nat(&self, n: u32) -> Result<(u32, u32), String> {
        let ctors = self.plain_inductive(n, 0)?;
        let [zero, succ] = ctors[..] else {
            return Err("it does not have two constructors".into());
        };
        if self.spelled(zero) != "Nat.zero" || self.spelled(succ) != "Nat.succ" {
            return Err("its constructors are not `Nat.zero`, `Nat.succ` in that order".into());
        }
        match self.env.get(zero) {
            Some(ConstantInfo::Constructor { typ, num_fields: 0, .. }) if is_const(typ, n) => {}
            _ => return Err("`Nat.zero` is not of type `Nat`".into()),
        }
        match self.env.get(succ) {
            Some(ConstantInfo::Constructor { typ, num_fields: 1, .. })
                if matches!(&***typ, ExprData::Pi(_, d, r) if is_const(d, n) && is_const(r, n)) => {}
            _ => return Err("`Nat.succ` is not of type `Nat → Nat`".into()),
        }
        Ok((zero, succ))
    }

    /// `inductive Bool : Type | false | true`, in that order.
    fn validate_bool(&self, n: u32) -> Result<(u32, u32), String> {
        let ctors = self.plain_inductive(n, 0)?;
        let [f, t] = ctors[..] else {
            return Err("it does not have two constructors".into());
        };
        if self.spelled(f) != "Bool.false" || self.spelled(t) != "Bool.true" {
            return Err("its constructors are not `Bool.false`, `Bool.true` in that order".into());
        }
        for k in [f, t] {
            match self.env.get(k) {
                Some(ConstantInfo::Constructor { typ, num_fields: 0, .. }) if is_const(typ, n) => {}
                _ => return Err("a constructor is not of type `Bool`".into()),
            }
        }
        Ok((f, t))
    }

    /// `inductive Decidable (p : Prop) : Type | isFalse (h : _) | isTrue (h : p)`.
    /// Returns the constructors and the type of `isFalse`'s field, stated
    /// under the binder for `p`. That type is `¬p` in Lean; what it is does
    /// not matter here, because the rules are checked against it as declared.
    fn validate_decidable(&self, n: u32) -> Result<(u32, u32, Expr), String> {
        let ctors = self.plain_inductive(n, 1)?;
        let [f, t] = ctors[..] else {
            return Err("it does not have two constructors".into());
        };
        if self.spelled(f) != "Decidable.isFalse" || self.spelled(t) != "Decidable.isTrue" {
            return Err("its constructors are not `Decidable.isFalse`, `Decidable.isTrue` in that order".into());
        }
        let prop = level::zero();
        // `(p : Prop) → (h : field) → Decidable p`
        let field = |k: u32| -> Option<Expr> {
            let Some(ConstantInfo::Constructor { typ, num_params: 1, num_fields: 1, level_params, .. }) =
                self.env.get(k)
            else {
                return None;
            };
            if !level_params.is_empty() {
                return None;
            }
            let ExprData::Pi(_, p, rest) = &***typ else { return None };
            let ExprData::Pi(_, h, result) = &***rest else { return None };
            let ExprData::App(d, arg) = &***result else { return None };
            (is_sort(p, &prop) && is_const(d, n) && matches!(&***arg, ExprData::BVar(1))).then(|| h.clone())
        };
        let Some(false_field) = field(f) else {
            return Err("`Decidable.isFalse` is not `(p : Prop) → _ → Decidable p`".into());
        };
        match field(t) {
            Some(h) if matches!(&**h, ExprData::BVar(0)) => {}
            _ => return Err("`Decidable.isTrue` is not `(p : Prop) → p → Decidable p`".into()),
        }
        Ok((f, t, false_field))
    }

    /// The type of string literals: a one-constructor inductive in `Type`
    /// without parameters. (That a literal denotes an inhabitant is not
    /// established: see the report on `String.ofList`.)
    fn validate_string(&self, n: u32) -> V {
        let ctors = self.plain_inductive(n, 0)?;
        if ctors.len() != 1 {
            return no("it does not have one constructor");
        }
        Ok(())
    }

    /// An inductive type in `Type`, alone in its block, without universe
    /// parameters or indices, safe, with `num_params` parameters each a
    /// `Prop`. Returns its constructors.
    fn plain_inductive(&self, n: u32, num_params: u32) -> Result<Vec<u32>, String> {
        let Some(ConstantInfo::InductiveType {
            level_params,
            typ,
            num_params: np,
            num_indices: 0,
            all,
            ctors,
            is_unsafe: false,
            ..
        }) = self.env.get(n)
        else {
            return Err("it is not a safe inductive type without indices".into());
        };
        if !level_params.is_empty() || *np != num_params || all[..] != [n] {
            return Err("it has universe parameters, other parameters, or is in a mutual block".into());
        }
        let type1 = level::succ(level::zero());
        let mut t = typ.clone();
        for _ in 0..num_params {
            let next = match &**t {
                ExprData::Pi(_, d, r) if is_sort(d, &level::zero()) => r.clone(),
                _ => return Err("a parameter is not a `Prop`".into()),
            };
            t = next;
        }
        if !is_sort(&t, &type1) {
            return Err("it is not in `Type`".into());
        }
        for (i, k) in ctors.iter().enumerate() {
            match self.env.get(*k) {
                Some(ConstantInfo::Constructor { induct, cidx, num_params: knp, is_unsafe: false, level_params, .. })
                    if *induct == n && *cidx as usize == i && *knp == num_params && level_params.is_empty() => {}
                _ => return Err("a constructor record does not belong to it".into()),
            }
        }
        Ok(ctors.clone())
    }

    // ---------------- definitions ----------------

    /// `n` is a safe definition without universe parameters whose type is
    /// definitionally `ty`.
    fn monomorphic_def(&self, n: u32, ty: &Expr) -> V {
        let Some(ConstantInfo::Def { level_params, typ, is_unsafe: false, .. }) = self.env.get(n) else {
            return no("it is not a definition");
        };
        if !level_params.is_empty() {
            return no("it has universe parameters");
        }
        if !self.types_agree(typ, ty) {
            return no("it does not have the expected type");
        }
        Ok(())
    }

    fn nat(&self) -> Result<(u32, u32, u32), String> {
        match (self.ext.nat, self.ext.nat_ctors) {
            (Some(n), Some((z, s))) => Ok((n, z, s)),
            _ => Err("`Nat` is not validated".into()),
        }
    }

    fn bools(&self) -> Result<(u32, u32), String> {
        match (self.ext.bool_false, self.ext.bool_true) {
            (Some(f), Some(t)) => Ok((f, t)),
            _ => Err("`Bool` is not validated".into()),
        }
    }

    fn need(&self, op: ExtOp) -> Result<u32, String> {
        self.ext.id_of(op).ok_or_else(|| format!("`{}` is not validated", op.spelling()))
    }

    /// `pred 0 ≡ 0`, `pred (succ x) ≡ x`.
    fn validate_nat_pred(&self, f: u32) -> V {
        let (nat, zero, succ) = self.nat()?;
        self.monomorphic_def(f, &arrow(c(nat), c(nat)))?;
        let lam1 = |b: Expr| lams(&[c(nat)], b);
        let x = expr::bvar(0);
        self.equation("pred 0 ≡ 0", &expr::app(c(f), c(zero)), &c(zero))?;
        self.equation(
            "pred (succ x) ≡ x",
            &lam1(expr::app(c(f), expr::app(c(succ), x.clone()))),
            &lam1(x),
        )
    }

    /// `Nat.bitwise : (Bool → Bool → Bool) → Nat → Nat → Nat`, a definition.
    /// Not validated beyond that.
    fn validate_nat_bitwise(&self, f: u32) -> V {
        let (nat, _, _) = self.nat()?;
        let (bf, _) = self.bools()?;
        let Some(ConstantInfo::InductiveType { .. }) = self.env.get(nat) else {
            return no("`Nat` is not validated");
        };
        let bool_ty = match self.env.get(bf) {
            Some(ConstantInfo::Constructor { induct, .. }) => c(*induct),
            _ => return no("`Bool` is not validated"),
        };
        let fun = arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty));
        self.monomorphic_def(f, &arrow(fun, arrow(c(nat), arrow(c(nat), c(nat)))))
    }

    fn validate_op(&self, op: ExtOp, f: u32) -> V {
        match op {
            ExtOp::Ite | ExtOp::Dite => return self.validate_ite(op, f),
            ExtOp::Decide => return self.validate_decide(f),
            _ => {}
        }
        let (nat, zero, succ) = self.nat()?;
        let n = || c(nat);
        let z = || c(zero);
        let s = |e: Expr| expr::app(c(succ), e);
        let ap = |g: u32, a: Expr, b: Expr| expr::apps(c(g), &[a, b]);
        let lam1 = |b: Expr| lams(&[c(nat)], b);
        let lam2 = |b: Expr| lams(&[c(nat), c(nat)], b);
        // Under `lam1` the variable is `x`; under `lam2` they are `x`, `y`.
        let x1 = || expr::bvar(0);
        let x = || expr::bvar(1);
        let y = || expr::bvar(0);
        let nat2nat = arrow(n(), arrow(n(), n()));
        match op {
            ExtOp::NatAdd => {
                self.monomorphic_def(f, &nat2nat)?;
                self.equation("add x 0 ≡ x", &lam1(ap(f, x1(), z())), &lam1(x1()))?;
                self.equation(
                    "add x (succ y) ≡ succ (add x y)",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(s(ap(f, x(), y()))),
                )
            }
            ExtOp::NatSub => {
                let pred = self.ext.nat_pred.ok_or("`Nat.pred` is not validated")?;
                self.monomorphic_def(f, &nat2nat)?;
                self.equation("sub x 0 ≡ x", &lam1(ap(f, x1(), z())), &lam1(x1()))?;
                self.equation(
                    "sub x (succ y) ≡ pred (sub x y)",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(expr::app(c(pred), ap(f, x(), y()))),
                )
            }
            ExtOp::NatMul => {
                let add = self.need(ExtOp::NatAdd)?;
                self.monomorphic_def(f, &nat2nat)?;
                self.equation("mul x 0 ≡ 0", &lam1(ap(f, x1(), z())), &lam1(z()))?;
                self.equation(
                    "mul x (succ y) ≡ add (mul x y) x",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(ap(add, ap(f, x(), y()), x())),
                )
            }
            ExtOp::NatPow => {
                let mul = self.need(ExtOp::NatMul)?;
                self.monomorphic_def(f, &nat2nat)?;
                self.equation("pow x 0 ≡ 1", &lam1(ap(f, x1(), z())), &lam1(s(z())))?;
                self.equation(
                    "pow x (succ y) ≡ mul (pow x y) x",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(ap(mul, ap(f, x(), y()), x())),
                )
            }
            ExtOp::NatBeq | ExtOp::NatBle => {
                let (bf, bt) = self.bools()?;
                let bool_ty = match self.env.get(bf) {
                    Some(ConstantInfo::Constructor { induct, .. }) => c(*induct),
                    _ => return no("`Bool` is not validated"),
                };
                self.monomorphic_def(f, &arrow(n(), arrow(n(), bool_ty)))?;
                // The two differ only at `0, succ x`.
                let zero_succ = if op == ExtOp::NatBle { bt } else { bf };
                self.equation("f 0 0 ≡ true", &ap(f, z(), z()), &c(bt))?;
                self.equation("f 0 (succ x)", &lam1(ap(f, z(), s(x1()))), &lam1(c(zero_succ)))?;
                self.equation("f (succ x) 0 ≡ false", &lam1(ap(f, s(x1()), z())), &lam1(c(bf)))?;
                self.equation(
                    "f (succ x) (succ y) ≡ f x y",
                    &lam2(ap(f, s(x()), s(y()))),
                    &lam2(ap(f, x(), y())),
                )
            }
            ExtOp::NatShiftLeft => {
                let mul = self.need(ExtOp::NatMul)?;
                self.monomorphic_def(f, &nat2nat)?;
                let two = s(s(z()));
                self.equation("shiftLeft x 0 ≡ x", &lam1(ap(f, x1(), z())), &lam1(x1()))?;
                self.equation(
                    "shiftLeft x (succ y) ≡ shiftLeft (mul 2 x) y",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(ap(f, ap(mul, two, x()), y())),
                )
            }
            ExtOp::NatShiftRight => {
                let div = self.need(ExtOp::NatDiv)?;
                self.monomorphic_def(f, &nat2nat)?;
                let two = s(s(z()));
                self.equation("shiftRight x 0 ≡ x", &lam1(ap(f, x1(), z())), &lam1(x1()))?;
                self.equation(
                    "shiftRight x (succ y) ≡ div (shiftRight x y) 2",
                    &lam2(ap(f, x(), s(y()))),
                    &lam2(ap(div, ap(f, x(), y()), two)),
                )
            }
            ExtOp::NatLand | ExtOp::NatLor | ExtOp::NatXor => {
                let bitwise = self.ext.nat_bitwise.ok_or("`Nat.bitwise` is not validated")?;
                let (bf, bt) = self.bools()?;
                self.monomorphic_def(f, &nat2nat)?;
                let Some(ConstantInfo::Def { value, .. }) = self.env.get(f) else {
                    return no("it is not a definition");
                };
                let g = match &***value {
                    ExprData::App(h, g) if is_const(h, bitwise) => g.clone(),
                    _ => return no("its value is not `Nat.bitwise f`"),
                };
                let table: [bool; 4] = match op {
                    ExtOp::NatLand => [false, false, false, true],
                    ExtOp::NatLor => [false, true, true, true],
                    _ => [false, true, true, false],
                };
                let b = |v: bool| c(if v { bt } else { bf });
                for (i, want) in table.iter().enumerate() {
                    let (p, q) = (i & 2 != 0, i & 1 != 0);
                    self.equation("truth table", &expr::apps(g.clone(), &[b(p), b(q)]), &b(*want))?;
                }
                Ok(())
            }
            // The name is trusted, as in Lean's kernel: a definition of the
            // right type and nothing more.
            ExtOp::NatDiv | ExtOp::NatMod | ExtOp::NatModCore | ExtOp::NatGcd => {
                self.monomorphic_def(f, &nat2nat)
            }
            ExtOp::Ite | ExtOp::Dite | ExtOp::Decide => unreachable!(),
        }
    }

    /// `ite c (isTrue h) t e ≡ t` and `ite c (isFalse h) t e ≡ e`, or for
    /// `dite` the branches applied to `h`, with every argument a variable
    /// and at the definition's own universe parameter. `try_dite` rewrites
    /// exactly these left-hand sides.
    fn validate_ite(&self, op: ExtOp, f: u32) -> V {
        let (is_false, is_true) = match (self.ext.decidable_is_false, self.ext.decidable_is_true) {
            (Some(a), Some(b)) => (a, b),
            _ => return no("`Decidable` is not validated"),
        };
        let dec = match self.env.get(is_true) {
            Some(ConstantInfo::Constructor { induct, .. }) => *induct,
            _ => return no("`Decidable` is not validated"),
        };
        let (_, _, false_field) = self.validate_decidable(dec)?;
        let Some(ConstantInfo::Def { level_params, is_unsafe: false, .. }) = self.env.get(f) else {
            return no("it is not a definition");
        };
        let [u] = level_params[..] else {
            return no("it does not have one universe parameter");
        };
        let head = expr::const_(f, vec![level::param(u)]);
        let sort_u = expr::sort(level::param(u));
        let prop = expr::sort(level::zero());
        let b = expr::bvar;
        for (ctor, taken) in [(is_true, true), (is_false, false)] {
            // `fun (α : Sort u) (c : Prop) (h : _) (t : _) (e : _) => …`;
            // below them α = 4, c = 3, h = 2, t = 1, e = 0.
            let h_ty = if taken { b(0) } else { false_field.clone() };
            let (t_ty, e_ty) = if op == ExtOp::Dite {
                // t : c → α, stated under α c h; e : field[c] → α, under α c h t.
                (
                    expr::pi(BinderInfo::Default, b(1), b(3)),
                    expr::pi(BinderInfo::Default, expr::instantiate1(&false_field, &b(2)), b(4)),
                )
            } else {
                (b(2), b(3))
            };
            let tys = [sort_u.clone(), prop.clone(), h_ty, t_ty, e_ty];
            let inst = expr::apps(c(ctor), &[b(3), b(2)]);
            let lhs = expr::apps(head.clone(), &[b(4), b(3), inst, b(1), b(0)]);
            let branch = if taken { b(1) } else { b(0) };
            let rhs = if op == ExtOp::Dite { expr::app(branch, b(2)) } else { branch };
            let what = if taken { "at `isTrue`" } else { "at `isFalse`" };
            self.equation(what, &lams(&tys, lhs), &lams(&tys, rhs))?;
        }
        Ok(())
    }

    /// `decide p (isTrue h) ≡ true`, `decide p (isFalse h) ≡ false`.
    fn validate_decide(&self, f: u32) -> V {
        let (is_false, is_true) = match (self.ext.decidable_is_false, self.ext.decidable_is_true) {
            (Some(a), Some(b)) => (a, b),
            _ => return no("`Decidable` is not validated"),
        };
        let (bf, bt) = self.bools()?;
        let dec = match self.env.get(is_true) {
            Some(ConstantInfo::Constructor { induct, .. }) => *induct,
            _ => return no("`Decidable` is not validated"),
        };
        let (_, _, false_field) = self.validate_decidable(dec)?;
        match self.env.get(f) {
            Some(ConstantInfo::Def { level_params, is_unsafe: false, .. }) if level_params.is_empty() => {}
            _ => return no("it is not a definition without universe parameters"),
        }
        let prop = expr::sort(level::zero());
        let b = expr::bvar;
        for (ctor, h_ty, value) in [(is_true, b(0), bt), (is_false, false_field, bf)] {
            // `fun (p : Prop) (h : _) => decide p (ctor p h)`
            let tys = [prop.clone(), h_ty];
            let lhs = expr::apps(c(f), &[b(1), expr::apps(c(ctor), &[b(1), b(0)])]);
            self.equation("decide at a constructor", &lams(&tys, lhs), &lams(&tys, c(value)))?;
        }
        Ok(())
    }

    // ---------------- the checks themselves ----------------

    fn types_agree(&self, a: &Expr, b: &Expr) -> bool {
        self.attempt(|tc| tc.is_def_eq(&Ctx::new(), a, b))
    }

    /// `lhs ≡ rhs`, both closed and well typed at one type, by the reduction
    /// every declaration is checked with.
    fn equation(&self, what: &str, lhs: &Expr, rhs: &Expr) -> V {
        let holds = self.attempt(|tc| {
            let ctx = Ctx::new();
            let tl = tc.infer_type(&ctx, lhs)?;
            let tr = tc.infer_type(&ctx, rhs)?;
            Ok(tc.is_def_eq(&ctx, &tl, &tr)? && tc.is_def_eq(&ctx, lhs, rhs)?)
        });
        if holds {
            Ok(())
        } else {
            Err(format!("{what} does not hold for its definition"))
        }
    }

    /// One question put to a fresh checker, as a declaration would put it:
    /// the eager pass, then Lean's lazy δ if that one does not say yes
    /// (`Checker::check_decl`). Anything but a yes is a no.
    fn attempt(&self, question: impl Fn(&Checker) -> R<bool>) -> bool {
        let ask = |lazy: bool| -> bool {
            let tc = Checker::with_extensions(self.env, self.names, self.ext).with_proof_store(self.proofs);
            // The context numbering `check_decl_once_go` resets before a
            // declaration; the next declaration resets it again. The
            // substitution memos are keyed by term identity and stay.
            CTX_IDS.with(|m| expr::clear_memo(&mut m.borrow_mut()));
            CTX_NEXT.with(|n| n.set(1));
            CORE_ABORTED.with(|a| a.set(false));
            let was = LAZY_MAIN_PATH.with(|l| l.replace(lazy));
            let r = question(&tc);
            LAZY_MAIN_PATH.with(|l| l.set(was));
            matches!(r, Ok(true))
        };
        ask(false) || ask(true)
    }
}

/// The table every build used before validation existed: each constant taken
/// at its name, `Nat`'s constructors by position. Unit tests build small
/// environments by hand and check reductions in them; this keeps those
/// environments meaning what they meant.
#[cfg(test)]
pub fn trusting_names(
    env: &Environment,
    names: &[Rc<String>],
    nat_ref: Option<u32>,
    string_ref: Option<u32>,
) -> Extensions {
    let find = |s: &str| names.iter().position(|n| n.as_str() == s).map(|i| i as u32);
    let mut ext = Extensions::default();
    ext.nat = nat_ref;
    ext.string = string_ref;
    if let Some(ConstantInfo::InductiveType { ctors, .. }) = nat_ref.and_then(|n| env.get(n)) {
        if ctors.len() == 2 {
            ext.nat_ctors = Some((ctors[0], ctors[1]));
        }
    }
    ext.bool_false = find("Bool.false");
    ext.bool_true = find("Bool.true");
    ext.decidable_is_false = find("Decidable.isFalse");
    ext.decidable_is_true = find("Decidable.isTrue");
    ext.nat_pred = find("Nat.pred");
    ext.nat_bitwise = find("Nat.bitwise");
    for op in ExtOp::ALL {
        if let Some(n) = find(op.spelling()) {
            ext.enable(op, n);
        }
    }
    ext
}
