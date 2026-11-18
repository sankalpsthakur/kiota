//! `infer_app_spine` (`KIOTA_SPINE`) against the one-argument rule.

use super::*;
use crate::env::ReducibilityHints;

const N: u32 = 0;
const Z: u32 = 1;
const O: u32 = 2;
const P: u32 = 3;
const PZ: u32 = 4;
const PO: u32 = 5;
const G: u32 = 6;
const T: u32 = 7;
const F: u32 = 8;
const Q: u32 = 9;
const H: u32 = 10;
const S: u32 = 11;
const S_MK: u32 = 12;
const S_Z: u32 = 13;
const W: u32 = 14;
const W_MK: u32 = 15;
const W_Z: u32 = 16;

fn c(i: u32) -> Expr {
    expr::const_(i, vec![])
}

fn pi(d: Expr, r: Expr) -> Expr {
    expr::pi(BinderInfo::Default, d, r)
}

fn lam(d: Expr, r: Expr) -> Expr {
    expr::lam(BinderInfo::Default, d, r)
}

/// ```text
/// N : Type        z o : N        P : N → Prop        pz : P z    po : P o
/// g : (n : N) → P n → N → N
/// T : Type := N → N              f : N → T
/// Q : (n : N) → P n → Prop       h : (n : N) → (p : P n) → Q n p
/// structure S (n : N) : Type where  a : N   b : P a   c : Q a b     sz : S z
/// structure W (n : N) : Prop where  a : N   b : P n                 wz : W z
/// ```
fn fixture() -> (Environment, Vec<Rc<String>>) {
    let mut env = Environment::default();
    let v = expr::bvar;
    let type1 = expr::sort(level::succ(level::zero()));
    let prop = expr::sort(level::zero());
    let axioms = [
        (N, type1.clone()),
        (Z, c(N)),
        (O, c(N)),
        (P, pi(c(N), prop.clone())),
        (PZ, expr::app(c(P), c(Z))),
        (PO, expr::app(c(P), c(O))),
        (G, pi(c(N), pi(expr::app(c(P), v(0)), pi(c(N), c(N))))),
        (F, pi(c(N), c(T))),
        (Q, pi(c(N), pi(expr::app(c(P), v(0)), prop))),
        (H, pi(c(N), pi(expr::app(c(P), v(0)), expr::apps(c(Q), &[v(1), v(0)])))),
    ];
    for (name, typ) in axioms {
        env.insert(name, ConstantInfo::Axiom { level_params: vec![], typ, is_unsafe: false });
    }
    env.insert(T, ConstantInfo::Def {
        level_params: vec![],
        typ: type1,
        value: pi(c(N), c(N)),
        hints: ReducibilityHints::Regular(1),
        is_unsafe: false,
    });
    // S.mk : (n : N) → (a : N) → (b : P a) → (c : Q a b) → S n
    env.insert(S, ConstantInfo::InductiveType {
        level_params: vec![],
        typ: pi(c(N), expr::sort(level::succ(level::zero()))),
        num_params: 1,
        num_indices: 0,
        all: vec![S],
        ctors: vec![S_MK],
        is_rec: false,
        is_unsafe: false,
    });
    env.insert(S_MK, ConstantInfo::Constructor {
        level_params: vec![],
        typ: pi(
            c(N),
            pi(
                c(N),
                pi(
                    expr::app(c(P), v(0)),
                    pi(expr::apps(c(Q), &[v(1), v(0)]), expr::app(c(S), v(3))),
                ),
            ),
        ),
        induct: S,
        cidx: 0,
        num_params: 1,
        num_fields: 3,
        is_unsafe: false,
    });
    env.insert(S_Z, ConstantInfo::Axiom {
        level_params: vec![],
        typ: expr::app(c(S), c(Z)),
        is_unsafe: false,
    });
    // W.mk : (n : N) → (a : N) → (b : P n) → W n, a Prop with a data field.
    env.insert(W, ConstantInfo::InductiveType {
        level_params: vec![],
        typ: pi(c(N), expr::sort(level::zero())),
        num_params: 1,
        num_indices: 0,
        all: vec![W],
        ctors: vec![W_MK],
        is_rec: false,
        is_unsafe: false,
    });
    env.insert(W_MK, ConstantInfo::Constructor {
        level_params: vec![],
        typ: pi(c(N), pi(c(N), pi(expr::app(c(P), v(1)), expr::app(c(W), v(2))))),
        induct: W,
        cidx: 0,
        num_params: 1,
        num_fields: 2,
        is_unsafe: false,
    });
    env.insert(W_Z, ConstantInfo::Axiom {
        level_params: vec![],
        typ: expr::app(c(W), c(Z)),
        is_unsafe: false,
    });
    let names = [
        "N", "z", "o", "P", "pz", "po", "g", "T", "f", "Q", "h", "S", "S.mk", "sz", "W", "W.mk",
        "wz",
    ]
        .iter()
        .map(|name| Rc::new((*name).to_owned()))
        .collect();
    (env, names)
}

/// A checker with the spine walk on (and verifying itself) and one with the
/// one-argument rule, over the same environment.
fn pair<'e>(env: &'e Environment, names: &'e [Rc<String>]) -> (Checker<'e>, Checker<'e>) {
    let on = Checker::new(env, names, None, None);
    on.spine.set(true);
    on.spine_verify.set(true);
    let off = Checker::new(env, names, None, None);
    off.spine.set(false);
    (on, off)
}

fn is_reject<X: std::fmt::Debug>(r: &R<X>) -> bool {
    matches!(r, Err(TcError::Reject(_)))
}

#[test]
fn spine_type_is_the_one_argument_rules_node() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    let ctx = Ctx::new();
    let terms = [
        // Dependent domain: the second argument's type mentions the first.
        expr::apps(c(G), &[c(Z), c(PZ), c(O)]),
        // Dependent result.
        expr::apps(c(H), &[c(O), c(PO)]),
        // The second binder is reached only by unfolding `T`.
        expr::apps(c(F), &[c(Z), c(O)]),
        // Partial applications.
        expr::apps(c(G), &[c(Z)]),
        expr::apps(c(G), &[c(O), c(PO)]),
        // A beta-redex head and an argument that is itself a spine.
        expr::apps(lam(c(N), expr::apps(c(G), &[expr::bvar(0)])), &[c(Z), c(PZ), c(O)]),
        expr::apps(c(G), &[c(Z), c(PZ), expr::apps(c(G), &[c(O), c(PO), c(Z)])]),
    ];
    for t in &terms {
        let a = on.infer_type(&ctx, t).unwrap();
        let b = off.infer_type(&ctx, t).unwrap();
        assert!(Rc::ptr_eq(&a, &b), "{}: {} vs {}", on.pp(t), on.pp(&a), on.pp(&b));
    }
    let ty = on.infer_type(&ctx, &terms[0]).unwrap();
    assert!(Rc::ptr_eq(&ty, &c(N)));
    let ty = on.infer_type(&ctx, &terms[1]).unwrap();
    assert!(Rc::ptr_eq(&ty, &expr::apps(c(Q), &[c(O), c(PO)])));
}

#[test]
fn spine_rejects_a_wrong_argument_wherever_it_sits() {
    let (env, names) = fixture();
    let ctx = Ctx::new();
    let bad = [
        // Middle: `po : P o` where `P z` is expected.
        expr::apps(c(G), &[c(Z), c(PO), c(O)]),
        // Last: a proof where an `N` is expected.
        expr::apps(c(G), &[c(Z), c(PZ), c(PZ)]),
        // First.
        expr::apps(c(G), &[c(PZ), c(PZ), c(O)]),
        // After a binder reached by unfolding.
        expr::apps(c(F), &[c(Z), c(PZ)]),
        // One argument too many: `N` is not a function type.
        expr::apps(c(G), &[c(Z), c(PZ), c(O), c(O)]),
        // Wrong argument inside an argument.
        expr::apps(c(G), &[c(Z), c(PZ), expr::apps(c(G), &[c(O), c(PZ), c(Z)])]),
    ];
    for t in &bad {
        // Fresh checkers: nothing cached decides it.
        let (on, off) = pair(&env, &names);
        assert!(is_reject(&off.infer_type(&ctx, t)), "one-argument rule accepts {}", off.pp(t));
        assert!(is_reject(&on.infer_type(&ctx, t)), "spine walk accepts {}", on.pp(t));
        // And again, now that prefix states exist.
        assert!(is_reject(&on.infer_type(&ctx, t)), "spine walk accepts {} on a retry", on.pp(t));
    }
}

#[test]
fn spine_under_binders_matches_and_rejects() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    let ctx = Ctx::new();
    let v = expr::bvar;
    let p_of = |i| expr::app(c(P), v(i));
    // fun (n : N) (hn : P n) (m : N) => g n hn m
    let good = lam(c(N), lam(p_of(0), lam(c(N), expr::apps(c(G), &[v(2), v(1), v(0)]))));
    // fun (n : N) (hn : P n) => h n hn : (n : N) → (hn : P n) → Q n hn
    let good_dep = lam(c(N), lam(p_of(0), expr::apps(c(H), &[v(1), v(0)])));
    for t in [&good, &good_dep] {
        let a = on.infer_type(&ctx, t).unwrap();
        let b = off.infer_type(&ctx, t).unwrap();
        assert!(Rc::ptr_eq(&a, &b), "{} vs {}", on.pp(&a), on.pp(&b));
    }
    // fun (n k : N) (hn : P n) => g k hn n: `hn : P n` where `P k` is expected.
    let bad = lam(c(N), lam(c(N), lam(p_of(1), expr::apps(c(G), &[v(1), v(0), v(2)]))));
    assert!(is_reject(&off.infer_type(&ctx, &bad)));
    assert!(is_reject(&on.infer_type(&ctx, &bad)));
    // The same spine `g #1 #0 #2` is well typed where bvar 0 proves `P #1`:
    // fun (n k : N) (hk : P k) => g k hk n. A state kept from the rejected
    // context must not decide this one, nor the other way round.
    let good_again = lam(c(N), lam(c(N), lam(p_of(0), expr::apps(c(G), &[v(1), v(0), v(2)]))));
    let a = on.infer_type(&ctx, &good_again).unwrap();
    let b = off.infer_type(&ctx, &good_again).unwrap();
    assert!(Rc::ptr_eq(&a, &b));
    assert!(is_reject(&on.infer_type(&ctx, &bad)));
}

#[test]
fn spine_resumes_from_a_shared_prefix() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    let ctx = Ctx::new();
    let prefix = expr::apps(c(G), &[c(Z), c(PZ)]);
    let first = expr::app(prefix.clone(), c(O));
    let second = expr::app(prefix.clone(), c(Z));
    on.infer_type(&ctx, &first).unwrap();
    let key = (0, Checker::ptr_key(&prefix));
    let st = on.spine_cache.borrow().get(&key).cloned().expect("state of the shared prefix");
    assert!(st.checked);
    // Two binders stepped over, none substituted: `N → N` under `n`, `hn`.
    assert_eq!(st.pending, 2);
    assert!(Rc::ptr_eq(&st.ty, &pi(c(N), c(N))));
    let ty = on.infer_type(&ctx, &second).unwrap();
    assert!(Rc::ptr_eq(&ty, &off.infer_type(&ctx, &second).unwrap()));
    // The prefix on its own is the state with its pending arguments put in.
    let pt = on.infer_type(&ctx, &prefix).unwrap();
    assert!(Rc::ptr_eq(&pt, &off.infer_type(&ctx, &prefix).unwrap()));
    assert!(Rc::ptr_eq(&pt, &pi(c(N), c(N))));
    // A longer spine resumes from a whole term inferred earlier.
    let longer = expr::app(expr::apps(c(F), &[c(Z)]), c(O));
    on.infer_type(&ctx, &expr::apps(c(F), &[c(Z)])).unwrap();
    let lt = on.infer_type(&ctx, &longer).unwrap();
    assert!(Rc::ptr_eq(&lt, &c(N)));
}

#[test]
fn an_infer_only_walk_does_not_stand_in_for_a_check() {
    let (env, names) = fixture();
    let (on, _) = pair(&env, &names);
    // Infer-only on an ill-typed term is outside the one-argument rule's
    // contract too; the verifier has nothing to say about it.
    on.spine_verify.set(false);
    let ctx = Ctx::new();
    let bad = expr::apps(c(G), &[c(Z), c(PO), c(O)]);
    // Infer-only does not look at the arguments, so it answers `N`.
    let only = on.with_infer_only(|| on.infer_type(&ctx, &bad)).unwrap();
    assert!(Rc::ptr_eq(&only, &c(N)));
    let prefix = expr::apps(c(G), &[c(Z), c(PO)]);
    let st = on.spine_cache.borrow().get(&(0, Checker::ptr_key(&prefix))).cloned().unwrap();
    assert!(!st.checked);
    // The check must not resume from that state or reuse that type.
    assert!(is_reject(&on.infer_type(&ctx, &bad)));
    assert!(is_reject(&on.infer_type(&ctx, &prefix)));
    // A checked state survives a later infer-only walk over the same prefix.
    let good_prefix = expr::apps(c(G), &[c(Z), c(PZ)]);
    on.infer_type(&ctx, &expr::app(good_prefix.clone(), c(O))).unwrap();
    on.with_infer_only(|| on.infer_type(&ctx, &expr::app(good_prefix.clone(), c(Z)))).unwrap();
    let st = on.spine_cache.borrow().get(&(0, Checker::ptr_key(&good_prefix))).cloned().unwrap();
    assert!(st.checked);
}

#[test]
fn spine_states_die_with_the_declaration() {
    let (env, names) = fixture();
    let (on, _) = pair(&env, &names);
    let ctx = Ctx::new();
    let prefix = expr::apps(c(G), &[c(Z), c(PZ)]);
    on.infer_type(&ctx, &expr::app(prefix.clone(), c(O))).unwrap();
    let key = (0, Checker::ptr_key(&prefix));
    assert!(on.spine_cache.borrow().contains_key(&key));
    // Checking any declaration starts from empty per-declaration caches.
    on.check_decl(PZ, "axiom").unwrap();
    assert!(!on.spine_cache.borrow().contains_key(&key));
}

#[test]
fn projection_field_types_are_the_one_argument_rules_nodes() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    let ctx = Ctx::new();
    let v = expr::bvar;
    let sz = c(S_Z);
    let fld = |i, e: &Expr| expr::proj(S, i, e.clone());
    for i in 0..3 {
        let a = on.infer_type(&ctx, &fld(i, &sz)).unwrap();
        let b = off.infer_type(&ctx, &fld(i, &sz)).unwrap();
        assert!(Rc::ptr_eq(&a, &b), "field {i}: {} vs {}", on.pp(&a), on.pp(&b));
    }
    // Each field's type mentions the earlier fields as projections of `sz`.
    let t1 = on.infer_type(&ctx, &fld(1, &sz)).unwrap();
    assert!(Rc::ptr_eq(&t1, &expr::app(c(P), fld(0, &sz))));
    let t2 = on.infer_type(&ctx, &fld(2, &sz)).unwrap();
    assert!(Rc::ptr_eq(&t2, &expr::apps(c(Q), &[fld(0, &sz), fld(1, &sz)])));
    // Under binders, with an open parameter: fun (n : N) (x : S n) => x.2
    let open = lam(c(N), lam(expr::app(c(S), v(0)), fld(2, &v(0))));
    let a = on.infer_type(&ctx, &open).unwrap();
    let b = off.infer_type(&ctx, &open).unwrap();
    assert!(Rc::ptr_eq(&a, &b), "{} vs {}", on.pp(&a), on.pp(&b));
    // Out of range, and a projection used at the wrong type, still reject.
    assert!(is_reject(&on.infer_type(&ctx, &fld(3, &sz))));
    assert!(is_reject(&off.infer_type(&ctx, &fld(3, &sz))));
    let misuse = expr::apps(c(G), &[c(Z), fld(1, &sz), c(O)]);
    assert!(is_reject(&off.infer_type(&ctx, &misuse)));
    assert!(is_reject(&on.infer_type(&ctx, &misuse)));
    // Well typed: `sz.1 : P sz.0` is what `g sz.0` expects next.
    let fine = expr::apps(c(G), &[fld(0, &sz), fld(1, &sz), c(O)]);
    assert!(Rc::ptr_eq(&on.infer_type(&ctx, &fine).unwrap(), &off.infer_type(&ctx, &fine).unwrap()));
}

#[test]
fn projection_out_of_a_prop_structure_keeps_its_restrictions() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    let ctx = Ctx::new();
    let wz = c(W_Z);
    // The data field of a proof may not be projected; the proof field may.
    let data = expr::proj(W, 0, wz.clone());
    let proof = expr::proj(W, 1, wz);
    assert!(is_reject(&off.infer_type(&ctx, &data)));
    assert!(is_reject(&on.infer_type(&ctx, &data)));
    let a = on.infer_type(&ctx, &proof).unwrap();
    let b = off.infer_type(&ctx, &proof).unwrap();
    assert!(Rc::ptr_eq(&a, &b));
    assert!(Rc::ptr_eq(&a, &expr::app(c(P), c(Z))));
}

/// Past an interner reset the one-walk rule and the one-argument rule can
/// hold the same term in two allocations: here the substitution memo kept
/// across the reset (`KIOTA_XMEMO`) answers the one-argument rule with the
/// telescope it built before, and the walk builds the domain again. The
/// verifier compares terms, so it counts that and goes on.
#[test]
fn verify_takes_the_same_term_in_another_allocation() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    // Under binders `n : N`, `p : P n`, so no closed-term cache answers.
    let mut ctx = Ctx::new();
    ctx.push(c(N));
    ctx.push(expr::app(c(P), expr::bvar(0)));
    let e = expr::apps(c(H), &[expr::bvar(1), expr::bvar(0)]);
    let before = on.infer_type(&ctx, &e).unwrap();
    let [_, rebuilt0] = spine_verified();
    // A declaration boundary past the reset threshold, memos kept.
    on.infer_cache.borrow_mut().clear();
    on.spine_cache.borrow_mut().clear();
    assert!(expr::intern_clear_if_large(0));
    let after = on.infer_type(&ctx, &e).unwrap();
    let [_, rebuilt1] = spine_verified();
    assert!(rebuilt1 > rebuilt0, "the walk rebuilt a domain the memo still held");
    assert!(expr::structurally_equal(&before, &after));
    assert!(expr::structurally_equal(&after, &off.infer_type(&ctx, &e).unwrap()));
    // A wrong argument is still refused on that side of the reset.
    let bad = expr::apps(c(H), &[expr::bvar(1), c(PO)]);
    assert!(is_reject(&on.infer_type(&ctx, &bad)));
}

/// The same with nothing kept across the reset. The one-argument rule
/// substitutes `a` under the binder of `b` and then lowers it again, which
/// builds `a` anew through the intern table; the walk puts in the argument
/// as it stands. An argument allocated before the reset (every node of the
/// declaration being checked, when the reset is at its start) then has a
/// second allocation on the one-argument side.
#[test]
fn verify_takes_an_argument_the_one_argument_rule_rebuilt() {
    let (env, names) = fixture();
    let (on, off) = pair(&env, &names);
    // n a : N, b : P a, c : Q a b  ⊢  S.mk n a b c : S n
    let v = expr::bvar;
    let mut ctx = Ctx::new();
    ctx.push(c(N));
    ctx.push(c(N));
    ctx.push(expr::app(c(P), v(0)));
    ctx.push(expr::apps(c(Q), &[v(1), v(0)]));
    let e = expr::apps(c(S_MK), &[v(3), v(2), v(1), v(0)]);
    let [_, rebuilt0] = spine_verified();
    let before = on.infer_type(&ctx, &e).unwrap();
    assert_eq!(spine_verified()[1], rebuilt0, "one generation: one node per term");
    // A declaration boundary past the reset threshold: nothing is kept.
    on.infer_cache.borrow_mut().clear();
    on.spine_cache.borrow_mut().clear();
    on.whnf_cache.borrow_mut().clear();
    expr::clear_subst_memos();
    assert!(expr::intern_clear_if_large(0));
    let after = on.infer_type(&ctx, &e).unwrap();
    assert!(spine_verified()[1] > rebuilt0, "the domain of `c` holds `a` in two allocations");
    assert!(expr::structurally_equal(&before, &after));
    assert!(expr::structurally_equal(&after, &off.infer_type(&ctx, &e).unwrap()));
    let bad = expr::apps(c(S_MK), &[v(3), v(2), v(1), v(1)]);
    assert!(is_reject(&on.infer_type(&ctx, &bad)));
}

/// The verifier compares terms, not judgments: a definitionally equal but
/// different term (`T` for `N → N`) is a divergence.
#[test]
#[should_panic(expected = "instead of")]
fn verify_refuses_another_term() {
    let (env, names) = fixture();
    let (on, _) = pair(&env, &names);
    let ctx = Ctx::new();
    let unfolded = pi(c(N), c(N));
    assert!(on.is_def_eq(&ctx, &c(T), &unfolded).unwrap());
    on.spine_verify_same(&c(T), &unfolded, || "domain".to_owned());
}
