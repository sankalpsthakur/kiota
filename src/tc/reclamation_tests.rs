use super::*;

fn fixture() -> (Environment, Vec<Rc<String>>) {
    let mut env = Environment::default();
    let a = expr::const_(0, vec![]);
    let b = expr::const_(1, vec![]);
    for (name, typ) in [
        (0, expr::sort(level::succ(level::zero()))),
        (1, expr::sort(level::succ(level::zero()))),
        (2, a.clone()),
        (3, b),
        (4, expr::pi(expr::BinderInfo::Default, a.clone(), a)),
    ] {
        env.insert(name, ConstantInfo::Axiom { level_params: vec![], typ, is_unsafe: false });
    }
    let names = ["A", "B", "a", "b", "f"].iter()
        .map(|name| Rc::new((*name).to_owned())).collect();
    (env, names)
}

#[test]
fn stale_source_entries_do_not_match_reconstructed_or_malformed_terms() {
    let (env, names) = fixture();
    let tc = Checker::new(&env, &names, None, None);
    let ctx = Ctx::new();
    for force in [false, true] {
        FORCE_EAGER_DEFEQ.with(|mode| mode.set(force));
        let old = expr::let_(expr::const_(0, vec![]), expr::const_(2, vec![]), expr::bvar(0));
        let old_id = expr::identity(&old);
        tc.infer_type_cached(&ctx, &old).unwrap();
        tc.whnf(&ctx, &old).unwrap();
        assert!(tc.is_def_eq_inner(&ctx, &old, &expr::const_(2, vec![])).unwrap());
        drop(old);
        // Deliberately preserve Tc cache entries while removing intern owners.
        expr::intern_clear_if_large(0);
        let rebuilt = expr::let_(expr::const_(0, vec![]), expr::const_(2, vec![]), expr::bvar(0));
        assert_ne!(old_id, expr::identity(&rebuilt));
        assert!(tc.is_def_eq_inner(&ctx, &rebuilt, &expr::const_(2, vec![])).unwrap());
        let malformed = expr::let_(expr::const_(0, vec![]), expr::const_(3, vec![]), expr::bvar(0));
        assert!(matches!(tc.infer_type_cached(&ctx, &malformed), Err(TcError::Reject(_))));
        assert!(!tc.is_def_eq_inner(&ctx, &malformed, &expr::const_(2, vec![])).unwrap());
    }
    FORCE_EAGER_DEFEQ.with(|mode| mode.set(false));
}

#[test]
fn reconstructed_context_type_cannot_reuse_a_different_inference_context() {
    let (env, names) = fixture();
    let tc = Checker::new(&env, &names, None, None);
    // Retain the query across reclamation. Its identity must not independently
    // save us from a stale context key. The open binding's shifted inferred
    // type retains its children but not the original Pi allocation.
    let query = expr::bvar(0);
    let universe = expr::sort(level::succ(level::zero()));
    let binding = expr::pi(expr::BinderInfo::Default, expr::bvar(0), expr::bvar(1));
    let weak_binding = Rc::downgrade(&binding);
    let mut old = Ctx::new();
    old.push(universe.clone());
    old.push(binding);
    let old_id = old.id;
    let old_type = tc.infer_type_cached(&old, &query).unwrap();
    drop(old);
    expr::intern_clear_if_large(0);
    assert!(weak_binding.upgrade().is_none());
    let mut new = Ctx::new();
    new.push(universe);
    let binding = expr::pi(expr::BinderInfo::Default, expr::bvar(0),
        expr::pi(expr::BinderInfo::Default, expr::bvar(1), expr::bvar(2)));
    new.push(binding.clone());
    assert_ne!(old_id, new.id);
    let actual = tc.infer_type_cached(&new, &query).unwrap();
    assert!(Rc::ptr_eq(&actual, &expr::shift(&binding, 1, 0)));
    assert!(!Rc::ptr_eq(&old_type, &actual));
}

#[test]
fn eviction_from_child_inference_does_not_promote_an_infer_only_result() {
    let (env, names) = fixture();
    let tc = Checker::new(&env, &names, None, None);
    let ctx = Ctx::new();
    let bad = expr::app(expr::const_(4, vec![]), expr::const_(3, vec![]));
    for force in [false, true] {
        FORCE_EAGER_DEFEQ.with(|mode| mode.set(force));
        tc.with_infer_only(|| tc.infer_type_cached(&ctx, &bad)).unwrap();
        let cache = if force { &tc.eager_infer_cache } else { &tc.infer_cache };
        {
            let mut memo = cache.borrow_mut();
            for n in 0..50_000 {
                memo.insert((u64::MAX, n), (expr::const_(0, vec![]), false));
            }
        }
        assert!(matches!(tc.infer_type_cached(&ctx, &bad), Err(TcError::Reject(_))));
        if expr::reclamation_enabled() {
            assert!(cache.borrow().len() < 50_000, "a child insertion must have evicted the table");
        }
    }
    FORCE_EAGER_DEFEQ.with(|mode| mode.set(false));
}

#[test]
fn iota_memo_does_not_reuse_discarded_motive_or_minor_identities() {
    let (env, names) = fixture();
    let tc = Checker::new(&env, &names, None, None);
    let motive = expr::lam(expr::BinderInfo::Default, expr::const_(0, vec![]), expr::bvar(0));
    let minor = expr::lam(expr::BinderInfo::Default, expr::const_(1, vec![]), expr::bvar(0));
    let key = Checker::iota_lit_memo_key(5, &[], &[motive.clone()], &[minor.clone()], &7u32.into());
    tc.iota_lit_memo.borrow_mut().insert(key.clone(), expr::const_(2, vec![]));
    drop(motive);
    drop(minor);
    assert!(expr::intern_clear_if_large(0));
    let motive = expr::lam(expr::BinderInfo::Default, expr::const_(0, vec![]), expr::bvar(0));
    let minor = expr::lam(expr::BinderInfo::Default, expr::const_(1, vec![]), expr::bvar(0));
    let rebuilt = Checker::iota_lit_memo_key(5, &[], &[motive], &[minor], &7u32.into());
    assert_ne!(key.2, rebuilt.2);
    assert_ne!(key.3, rebuilt.3);
    let memo = tc.iota_lit_memo.borrow();
    assert!(memo.contains_key(&key), "stale entry deliberately remains");
    assert!(!memo.contains_key(&rebuilt));
}
