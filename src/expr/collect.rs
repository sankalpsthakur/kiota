//! Experimental batched collection of strong-interner lookup ownership.
//! Only remove a node when the interner owns its last strong reference.
//! Releasing a parent makes its otherwise unused children eligible in turn.
//! Roots held by the environment, a cache, or active evaluation remain interned.
use super::{hash_node, identity, Expr, ExprData, Interner};
use std::rc::Rc;

impl Interner {
    pub(super) fn collect_dead(&mut self) -> usize {
        let mut pending: Vec<(u64, usize)> = self.primary.iter()
            .filter(|(_, node)| Rc::strong_count(node) == 1)
            .map(|(&hash, node)| (hash, identity(node))).collect();
        for (&hash, bucket) in &self.overflow {
            pending.extend(bucket.iter()
                .filter(|node| Rc::strong_count(node) == 1)
                .map(|node| (hash, identity(node))));
        }
        let mut collected = 0;
        while let Some((hash, id)) = pending.pop() {
            let removed = match self.primary.entry(hash) {
                std::collections::hash_map::Entry::Occupied(entry)
                    if identity(entry.get()) == id && Rc::strong_count(entry.get()) == 1 =>
                    Some(entry.remove()),
                _ => None,
            };
            let removed = removed.or_else(|| {
                let bucket = self.overflow.get_mut(&hash)?;
                let position = bucket.iter().position(|node|
                    identity(node) == id && Rc::strong_count(node) == 1)?;
                let node = bucket.swap_remove(position);
                if bucket.is_empty() {
                    self.overflow.remove(&hash);
                }
                Some(node)
            });
            if let Some(node) = removed {
                let mut queue = |child: &Expr| pending.push((hash_node(&child.data), identity(child)));
                match &node.data {
                    ExprData::App(f, a) => { queue(f); queue(a); }
                    ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
                        queue(ty); queue(body);
                    }
                    ExprData::Let(ty, val, body) => { queue(ty); queue(val); queue(body); }
                    ExprData::Proj(_, _, value) => queue(value),
                    _ => {}
                }
                // No child is retained by the worklist, so this drop releases
                // its parent reference before the child's eligibility check.
                drop(node);
                collected += 1;
            }
        }
        collected
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{alloc_node, BinderInfo};

    #[test]
    fn releases_an_unused_deep_dag_in_one_collection() {
        let mut pool = Interner::default();
        let atom = pool.intern(ExprData::BVar(0));
        let mut spine = atom.clone();
        for _ in 0..20_000 {
            spine = pool.intern(ExprData::App(spine, atom.clone()));
        }
        drop(spine);
        assert_eq!(pool.collect_dead(), 20_000);
        assert_eq!(pool.len(), 1);
        assert!(Rc::ptr_eq(&atom, &pool.intern(ExprData::BVar(0))));
    }

    #[test]
    fn external_parent_preserves_shared_children_and_identity() {
        let mut pool = Interner::default();
        let child = pool.intern(ExprData::BVar(1));
        let child_id = identity(&child);
        let live = pool.intern(ExprData::App(child.clone(), child.clone()));
        let dead = pool.intern(ExprData::Proj(2, 0, child.clone()));
        drop(child);
        drop(dead);
        assert_eq!(pool.collect_dead(), 1);
        let reconstructed = pool.intern(ExprData::BVar(1));
        assert_eq!(identity(&reconstructed), child_id);
        drop(reconstructed);
        drop(live);
        assert_eq!(pool.collect_dead(), 2);
        assert_eq!(pool.len(), 0);
    }

    #[test]
    fn collision_entries_are_removed_by_exact_identity() {
        let mut pool = Interner::default();
        let a = alloc_node(ExprData::BVar(11));
        let b = alloc_node(ExprData::BVar(12));
        let hash = hash_node(&ExprData::BVar(12));
        pool.primary.insert(hash, a.clone());
        pool.overflow.insert(hash, vec![b.clone()]);
        drop(a);
        assert_eq!(pool.collect_dead(), 1);
        assert!(Rc::ptr_eq(&b, &pool.intern(ExprData::BVar(12))));
        drop(b);
        assert_eq!(pool.collect_dead(), 1);
        assert_eq!(pool.len(), 0);
    }

    #[test]
    fn all_parent_kinds_release_only_unowned_children() {
        let mut pool = Interner::default();
        let ty = pool.intern(ExprData::BVar(2));
        let val = pool.intern(ExprData::BVar(3));
        let body = pool.intern(ExprData::BVar(4));
        let lam = pool.intern(ExprData::Lam(BinderInfo::Default, ty.clone(), body.clone()));
        let pi = pool.intern(ExprData::Pi(BinderInfo::Default, ty.clone(), body.clone()));
        let let_ = pool.intern(ExprData::Let(ty.clone(), val.clone(), body.clone()));
        let proj = pool.intern(ExprData::Proj(5, 0, val.clone()));
        drop(lam); drop(pi); drop(let_); drop(proj);
        assert_eq!(pool.collect_dead(), 4);
        assert_eq!(pool.len(), 3);
        drop(ty); drop(val); drop(body);
        assert_eq!(pool.collect_dead(), 3);
        assert_eq!(pool.len(), 0);
    }

    #[test]
    fn repeated_collection_cannot_recycle_persistent_keys() {
        let mut pool = Interner::default();
        let dead = pool.intern(ExprData::BVar(6));
        let old_id = identity(&dead);
        drop(dead);
        assert_eq!(pool.collect_dead(), 1);
        let new = pool.intern(ExprData::BVar(6));
        assert_ne!(identity(&new), old_id);
        assert_eq!(pool.collect_dead(), 0);
    }
}
