use super::*;
use crate::level;
use std::hash::BuildHasherDefault;

#[derive(Default)]
struct CollidingHasher;

impl Hasher for CollidingHasher {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
}

fn subst(bindings: &[(u32, u32)]) -> FxHashMap<u32, Level> {
    bindings
        .iter()
        .map(|&(n, value)| (n, level::mk_const(u64::from(value))))
        .collect()
}

#[test]
fn colliding_substitutions_never_share_an_id_or_result() {
    clear_subst_memos();
    let mut ids = std::collections::HashMap::with_hasher(
        BuildHasherDefault::<CollidingHasher>::default(),
    );
    let low = subst(&[(7, 0), (8, 1)]);
    let high = subst(&[(7, 2), (8, 1)]);
    let low_id = level_subst_id(&low, &mut ids);
    let high_id = level_subst_id(&high, &mut ids);
    assert_ne!(low_id, high_id, "equal hashes are not equal substitutions");
    assert_eq!(level_subst_id(&low, &mut ids), low_id);
    let term = sort(level::param(7));
    let a = instantiate_level_params_cached(&term, &low, low_id);
    let b = instantiate_level_params_cached(&term, &high, high_id);
    assert!(Rc::ptr_eq(&a, &sort(level::zero())));
    assert!(Rc::ptr_eq(&b, &sort(level::mk_const(2))));
    assert!(!Rc::ptr_eq(&a, &b));
    clear_subst_memos();
}

#[test]
fn insertion_order_and_equal_level_allocations_reuse_substitution() {
    clear_subst_memos();
    let first = subst(&[(7, 1), (8, 2)]);
    let second = subst(&[(8, 2), (7, 1)]);
    let term = const_(19, vec![level::param(7), level::param(8)]);
    let a = instantiate_level_params(&term, &first);
    let b = instantiate_level_params(&term, &second);
    assert!(Rc::ptr_eq(&a, &b));
    assert_eq!(LEVEL_SUBST_IDS.with(|ids| ids.borrow().len()), 1);
}

#[test]
fn clearing_substitutions_cannot_reuse_a_stale_expression_result() {
    clear_subst_memos();
    let term = sort(level::param(7));
    let old = instantiate_level_params(&term, &subst(&[(7, 1)]));
    clear_subst_memos();
    assert_eq!(LEVEL_INST_MEMO.with(|memo| memo.borrow().len()), 0);
    assert_eq!(LEVEL_SUBST_IDS.with(|ids| ids.borrow().len()), 0);
    let new = instantiate_level_params(&term, &subst(&[(7, 2)]));
    assert!(Rc::ptr_eq(&old, &sort(level::mk_const(1))));
    assert!(Rc::ptr_eq(&new, &sort(level::mk_const(2))));
    assert!(!Rc::ptr_eq(&old, &new));
}

#[test]
fn empty_substitution_preserves_the_original_node() {
    clear_subst_memos();
    let term = const_(11, vec![level::param(7)]);
    assert!(Rc::ptr_eq(&term, &instantiate_level_params(&term, &FxHashMap::default())));
    assert_eq!(LEVEL_SUBST_IDS.with(|ids| ids.borrow().len()), 0);
}

fn reference(e: &Expr, subst: &FxHashMap<u32, Level>) -> Expr {
    match &***e {
        ExprData::BVar(_) | ExprData::Lit(_) => e.clone(),
        ExprData::Sort(l) => sort(level::instantiate(l, subst)),
        ExprData::Const(n, us) => const_(*n, us.iter().map(|l| level::instantiate(l, subst)).collect()),
        ExprData::App(f, a) => app(reference(f, subst), reference(a, subst)),
        ExprData::Lam(bi, ty, body) => lam(*bi, reference(ty, subst), reference(body, subst)),
        ExprData::Pi(bi, ty, body) => pi(*bi, reference(ty, subst), reference(body, subst)),
        ExprData::Let(ty, val, body) => let_(reference(ty, subst), reference(val, subst), reference(body, subst)),
        ExprData::Proj(s, i, val) => proj(*s, *i, reference(val, subst)),
    }
}

#[test]
fn substitution_matches_reference_through_every_node_kind() {
    clear_subst_memos();
    let u = level::param(7);
    let v = level::param(8);
    let ty = sort(level::imax(u.clone(), v.clone()));
    let constant = const_(31, vec![u.clone(), level::max(u, v), level::param(9)]);
    let terms = vec![
        bvar(3), lit_nat(42u32.into()), lit_str("universe test"), ty.clone(), constant.clone(),
        app(constant.clone(), ty.clone()),
        lam(BinderInfo::Implicit, ty.clone(), app(constant.clone(), bvar(0))),
        pi(BinderInfo::Default, ty.clone(), constant.clone()),
        let_(ty.clone(), constant.clone(), app(bvar(0), ty)),
        proj(31, 0, constant),
    ];
    for bindings in [subst(&[(7, 0), (8, 1)]), subst(&[(7, 3), (8, 0)])] {
        for term in &terms {
            assert!(Rc::ptr_eq(&instantiate_level_params(term, &bindings), &reference(term, &bindings)));
        }
    }
}

#[test]
fn shared_dag_uses_one_substitution_identity() {
    clear_subst_memos();
    let mut term = const_(41, vec![level::param(7)]);
    for _ in 0..40 {
        term = app(term.clone(), term);
    }
    let result = instantiate_level_params(&term, &subst(&[(7, 2)]));
    assert!(!Rc::ptr_eq(&term, &result));
    assert_eq!(LEVEL_SUBST_IDS.with(|ids| ids.borrow().len()), 1);
    assert_eq!(LEVEL_INST_MEMO.with(|memo| memo.borrow().len()), 41);
}

#[test]
fn recursive_eviction_keeps_complete_universe_substitution_identity() {
    clear_subst_memos();
    let term = app(sort(level::param(7)), sort(level::param(8)));
    let low = subst(&[(7, 0), (8, 1)]);
    let high = subst(&[(7, 2), (8, 3)]);
    let prior = instantiate_level_params(&term, &low);
    LEVEL_INST_MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        for n in 0..50_000 {
            memo.insert((usize::MAX - n, usize::MAX), prior.clone());
        }
    });
    // A previously uncached child must insert and clear the full table while
    // the outer traversal retains its precomputed substitution ID.
    let outer = pi(BinderInfo::Default, sort(level::param(9)), term);
    let a = instantiate_level_params(&outer, &low);
    if reclamation_enabled() {
        assert!(LEVEL_INST_MEMO.with(|memo| memo.borrow().len()) < 50_000);
    }
    let b = instantiate_level_params(&outer, &high);
    assert_eq!(LEVEL_SUBST_IDS.with(|ids| ids.borrow().len()), 2);
    assert!(Rc::ptr_eq(&a, &reference(&outer, &low)));
    assert!(Rc::ptr_eq(&b, &reference(&outer, &high)));
    assert!(!Rc::ptr_eq(&a, &b));
    clear_subst_memos();
}

#[test]
fn retained_substitution_entries_do_not_match_reallocated_sources() {
    clear_subst_memos();
    let source = app(const_(51, vec![]), bvar(0));
    let source_id = identity(&source);
    let a = const_(52, vec![]);
    let first = instantiate1(&source, &a);
    let shifted = shift(&source, 1, 0);
    let old_inst_key = (source_id, identity(&a));
    let old_shift_key = (source_id, 1, 0);
    drop(source);
    assert!(intern_clear_if_large(0));
    let rebuilt = app(const_(51, vec![]), bvar(0));
    assert_ne!(source_id, identity(&rebuilt));
    // Keep every non-source key component fixed: only allocation identity
    // distinguishes the old source from its structurally equal reconstruction.
    let new_inst_key = (identity(&rebuilt), identity(&a));
    let new_shift_key = (identity(&rebuilt), 1, 0);
    assert!(INST1_MEMO.with(|memo| memo.borrow().contains_key(&old_inst_key)));
    assert!(SHIFT_MEMO.with(|memo| memo.borrow().contains_key(&old_shift_key)));
    assert!(!INST1_MEMO.with(|memo| memo.borrow().contains_key(&new_inst_key)));
    assert!(!SHIFT_MEMO.with(|memo| memo.borrow().contains_key(&new_shift_key)));
    let actual = instantiate1(&rebuilt, &a);
    assert!(Rc::ptr_eq(&actual, &app(const_(51, vec![]), a.clone())));
    assert!(matches!(&**first, ExprData::App(_, x) if Rc::ptr_eq(x, &a)));
    let new_shift = shift(&rebuilt, 1, 0);
    assert!(matches!(&**new_shift, ExprData::App(_, x) if matches!(&***x, ExprData::BVar(1))));
    assert!(matches!(&**shifted, ExprData::App(_, x) if matches!(&***x, ExprData::BVar(1))));
    clear_subst_memos();
}
