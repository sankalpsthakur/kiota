//! Opt-in weak interning for bounded eager-normalization experiments.
//! Live terms still hash-cons exactly; collecting dead lookup entries cannot
//! change a live term's identity. All persistent expression memo keys must use
//! `identity`, never recyclable allocator addresses.
use super::{alloc_node, hash_node, node_eq, Expr, ExprData, ExprNode};
use rustc_hash::FxHashMap;
use std::rc::Rc;

pub(super) struct WeakInterner {
    primary: FxHashMap<u64, std::rc::Weak<ExprNode>>,
    overflow: FxHashMap<u64, Vec<std::rc::Weak<ExprNode>>>,
    next_collection: usize,
}

impl Default for WeakInterner {
    fn default() -> Self {
        Self {
            primary: FxHashMap::default(),
            overflow: FxHashMap::default(),
            next_collection: 250_000,
        }
    }
}

impl WeakInterner {
    pub(super) fn intern(&mut self, data: ExprData) -> Expr {
        if self.len() >= self.next_collection {
            self.collect();
            self.next_collection = self.len().saturating_add(250_000);
        }
        let hash = hash_node(&data);
        let primary = self.primary.get(&hash).and_then(std::rc::Weak::upgrade);
        if let Some(node) = &primary {
            if node_eq(&data, node) {
                return node.clone();
            }
        }
        if let Some(bucket) = self.overflow.get(&hash) {
            for weak in bucket {
                if let Some(node) = weak.upgrade() {
                    if node_eq(&data, &node) {
                        return node;
                    }
                }
            }
        }
        let node = alloc_node(data);
        if primary.is_some() {
            self.overflow.entry(hash).or_default().push(Rc::downgrade(&node));
        } else {
            self.primary.insert(hash, Rc::downgrade(&node));
        }
        node
    }

    pub(super) fn len(&self) -> usize {
        self.primary.len() + self.overflow.values().map(Vec::len).sum::<usize>()
    }

    fn collect(&mut self) {
        self.primary.retain(|_, node| node.strong_count() != 0);
        self.overflow.retain(|_, bucket| {
            bucket.retain(|node| node.strong_count() != 0);
            !bucket.is_empty()
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{identity, ExprData};

    #[test]
    fn collecting_dead_entries_preserves_all_live_identity() {
        let mut pool = WeakInterner::default();
        let live = pool.intern(ExprData::BVar(3));
        let dead = pool.intern(ExprData::BVar(4));
        let discarded_identity = identity(&dead);
        drop(dead);
        pool.collect();
        assert_eq!(pool.len(), 1);
        assert!(Rc::ptr_eq(&live, &pool.intern(ExprData::BVar(3))));
        let replacement = pool.intern(ExprData::BVar(4));
        assert_ne!(discarded_identity, identity(&replacement));
    }

    #[test]
    fn live_hash_collisions_are_compared_exactly_after_collection() {
        let mut pool = WeakInterner::default();
        let a = alloc_node(ExprData::BVar(11));
        let b = alloc_node(ExprData::BVar(12));
        // Force the collision lookup path rather than depending on a lucky
        // hash collision. The differing primary is dead after dropping `a`.
        let hash = hash_node(&ExprData::BVar(12));
        pool.primary.insert(hash, Rc::downgrade(&a));
        pool.overflow.insert(hash, vec![Rc::downgrade(&b)]);
        assert!(Rc::ptr_eq(&b, &pool.intern(ExprData::BVar(12))));
        drop(a);
        pool.collect();
        assert!(Rc::ptr_eq(&b, &pool.intern(ExprData::BVar(12))));
    }

    #[test]
    fn automatic_collection_keeps_children_owned_only_by_live_parent() {
        let mut pool = WeakInterner::default();
        let child = pool.intern(ExprData::BVar(23));
        let parent = pool.intern(ExprData::App(child.clone(), child.clone()));
        let child_id = identity(&child);
        drop(child);
        let dead = pool.intern(ExprData::BVar(24));
        drop(dead);
        pool.next_collection = 0;
        let reconstructed = pool.intern(ExprData::BVar(23));
        assert_eq!(child_id, identity(&reconstructed));
        let ExprData::App(original, _) = &**parent else { panic!("app"); };
        assert!(Rc::ptr_eq(original, &reconstructed));
        assert_eq!(pool.len(), 2);
    }

    #[test]
    fn unequal_collision_candidate_is_never_reused() {
        let mut pool = WeakInterner::default();
        let different = alloc_node(ExprData::BVar(41));
        let hash = hash_node(&ExprData::BVar(42));
        pool.primary.insert(hash, Rc::downgrade(&different));
        let result = pool.intern(ExprData::BVar(42));
        assert!(!Rc::ptr_eq(&different, &result));
        assert!(matches!(&**result, ExprData::BVar(42)));
        assert!(Rc::ptr_eq(&result, &pool.intern(ExprData::BVar(42))));
    }

    #[test]
    fn deep_spine_drops_with_weak_entries_and_no_recursive_teardown() {
        let mut pool = WeakInterner::default();
        let atom = pool.intern(ExprData::BVar(0));
        let mut spine = atom.clone();
        for _ in 0..20_000 {
            spine = pool.intern(ExprData::App(spine, atom.clone()));
        }
        drop(spine);
        pool.collect();
        assert_eq!(pool.len(), 1);
        assert!(Rc::ptr_eq(&atom, &pool.intern(ExprData::BVar(0))));
    }
}
