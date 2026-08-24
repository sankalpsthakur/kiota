//! Closure-based normalization-by-evaluation (NbE), spiked behind
//! `KIOTA_NBE=1` for `is_def_eq` only.
//!
//! Why: the eager `whnf`/`instantiate` path represents "the recursive call
//! I haven't looked at yet" as a *substituted term* that gets rebuilt
//! (`instantiate1`/`shift`) and re-interned every time a `Nat.rec`/`brecOn`
//! step nests one level deeper. Interning shares *identical* syntax trees,
//! but a `below`/`brecOn` accumulator grows a new (structurally distinct)
//! wrapper at every level, so nothing is shared and the work is superlinear
//! in the numeral (`Nat.below` rebuilt per level, not shared — see PR
//! description). Raising the recursion-depth cap does not fix that; it was
//! tried and reverted (still declines, or "fixes" the decline into a run
//! that never finishes).
//!
//! NbE instead evaluates into `Value`s under `Closure`s (`body` + `env`,
//! *never* a substituted term). A `Value` referenced from two places is one
//! `Rc`, forced at most once (`Thunk`), so an accumulator that is genuinely
//! shared in the source stays shared in the value representation instead of
//! being independently rebuilt each time it is reached. Free/bound
//! variables are named by de Bruijn *level* (stable position from the root)
//! rather than *index* (position relative to the point of use), because an
//! index has to be renumbered every time a value moves under one more
//! binder — exactly the kind of "structurally distinct but semantically
//! identical" duplication that defeats hash-consing.
//!
//! Scope (this is a spike, not a rewrite): `eval`/`apply` implement the
//! core calculus (`Sort`/`Pi`/`Lam`/`App`/`Let`/`Proj`/`Const`-delta) plus
//! the *simple* shape of inductive iota — a major that is a literal `Nat`
//! or a fully-applied constructor of a type in the recursor's mutual group,
//! with zero-index recursors and no higher-order recursive occurrences
//! (i.e. `Nat.rec`/`List.rec`/`brecOn`-style structural recursion, which is
//! exactly the target case; `Acc.rec`/nested-functor recursion is out of
//! scope and just stays a stuck neutral). Everything this module cannot
//! confidently resolve — including every extension the eager `whnf_core`
//! dispatches to (omega, comm-ring, K-like, structure eta, Quot, …) — is
//! never asserted unequal: `is_def_eq_via_nbe` only trusts an `Ok(true)`
//! it derived from two values reducing to a matching canonical/neutral
//! shape, and defers to the (already-tested) eager comparator for anything
//! else, on both flags. NbE can therefore only *accelerate* an accept it
//! would eventually reach anyway; it can never turn an accept into a
//! different verdict.

use crate::expr::{BinderInfo, Expr, Lit};
use crate::level::Level;
use crate::tc::{Checker, R};
use std::cell::RefCell;
use std::rc::Rc;

/// `KIOTA_NBE=1` routes `is_def_eq` through this module. Default (unset) is
/// the untouched eager path, so existing behavior is bit-for-bit unchanged
/// unless the flag is set.
pub fn nbe_enabled() -> bool {
    thread_local! {
        static ON: bool = std::env::var_os("KIOTA_NBE").is_some();
    }
    ON.with(|b| *b)
}

/// `env[i]` is the thunk bound for de Bruijn index `i` counted from the
/// *innermost* binder — same convention `Ctx` uses, so `env.len()` is
/// always the current depth and doubles as the next fresh variable's level.
pub type VEnv = Rc<Vec<Rc<Thunk>>>;

pub fn empty_env() -> VEnv {
    Rc::new(Vec::new())
}

/// The "identity" environment of a given depth: index `i` (bvar counted
/// from the innermost binder) is bound to a fresh neutral variable whose
/// *level* is `depth - 1 - i`. Quoting a value at `depth` and re-evaluating
/// the quoted term against `generic_env(depth)` is the identity — this is
/// what lets internal reduction steps (e.g. iota) round-trip through a
/// small amount of quoting without renumbering bugs, even for open terms.
pub fn generic_env(depth: u32) -> VEnv {
    Rc::new((0..depth).map(|lvl| Thunk::forced(Rc::new(Value::Neutral(Neutral::Var(lvl))))).collect())
}

pub enum Value {
    Neutral(Neutral),
    Lam(BinderInfo, Rc<Thunk>, VEnv, Expr),
    Pi(BinderInfo, Rc<Thunk>, VEnv, Expr),
    Sort(Level),
    Lit(Lit),
}

/// A stuck spine: a free/bound variable or an opaque/undelta-able global,
/// applied to zero or more (lazy) arguments, or a stuck projection.
pub enum Neutral {
    Var(u32),
    Const(u32, Rc<Vec<Level>>),
    App(Rc<Neutral>, Rc<Thunk>),
    Proj(u32, u32, Rc<Neutral>),
}

enum ThunkState {
    Deferred(VEnv, Expr),
    /// A recursive-occurrence call built directly in value space by
    /// `Checker::build_rec_call_value`: re-invoking the recursor on the
    /// smaller field never re-serializes the accumulator to an `Expr`, and
    /// re-entering the same `(rname, us, params, motives, minors, field)`
    /// key elsewhere hits `Checker`'s iota memo instead of recomputing.
    RecCall {
        rname: u32,
        us: Rc<Vec<Level>>,
        params: Vec<Rc<Thunk>>,
        motives: Vec<Rc<Thunk>>,
        minors: Vec<Rc<Thunk>>,
        field: Rc<Thunk>,
        depth: u32,
    },
    Forced(Rc<Value>),
}

pub struct Thunk(RefCell<ThunkState>);

impl Thunk {
    pub fn deferred(env: VEnv, e: Expr) -> Rc<Thunk> {
        Rc::new(Thunk(RefCell::new(ThunkState::Deferred(env, e))))
    }

    pub fn forced(v: Rc<Value>) -> Rc<Thunk> {
        Rc::new(Thunk(RefCell::new(ThunkState::Forced(v))))
    }

    #[allow(clippy::too_many_arguments)]
    pub fn rec_call(
        rname: u32,
        us: Rc<Vec<Level>>,
        params: Vec<Rc<Thunk>>,
        motives: Vec<Rc<Thunk>>,
        minors: Vec<Rc<Thunk>>,
        field: Rc<Thunk>,
        depth: u32,
    ) -> Rc<Thunk> {
        Rc::new(Thunk(RefCell::new(ThunkState::RecCall {
            rname,
            us,
            params,
            motives,
            minors,
            field,
            depth,
        })))
    }

    /// Force-and-memoize. Never re-evaluates the same thunk twice: this is
    /// the whole sharing story — a value reached through two different
    /// `Rc<Thunk>` clones only pays evaluation once.
    pub fn force(&self, tc: &Checker) -> R<Rc<Value>> {
        if let ThunkState::Forced(v) = &*self.0.borrow() {
            return Ok(v.clone());
        }
        let computed = {
            let snapshot = {
                let st = self.0.borrow();
                match &*st {
                    ThunkState::Deferred(env, e) => Ok((env.clone(), e.clone())),
                    ThunkState::RecCall {
                        rname,
                        us,
                        params,
                        motives,
                        minors,
                        field,
                        depth,
                    } => Err((
                        *rname,
                        us.clone(),
                        params.clone(),
                        motives.clone(),
                        minors.clone(),
                        field.clone(),
                        *depth,
                    )),
                    ThunkState::Forced(v) => return Ok(v.clone()),
                }
            };
            match snapshot {
                Ok((env, e)) => tc.eval(&env, &e)?,
                Err((rname, us, params, motives, minors, field, depth)) => {
                    tc.build_rec_call_value(rname, &us, &params, &motives, &minors, &field, depth)?
                }
            }
        };
        *self.0.borrow_mut() = ThunkState::Forced(computed.clone());
        Ok(computed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nbe_flag_reads_env_once_per_process() {
        // Just exercises the thread-local without requiring the env var;
        // real on/off coverage lives in `tc::tests` where a `Checker` is
        // available to run `is_def_eq_via_nbe` end to end.
        let _ = nbe_enabled();
    }
}
