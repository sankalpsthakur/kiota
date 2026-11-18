use crate::level::Level;
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHasher};
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

mod reclaim;

/// Experimental only: retain no strong references in the interner and bound
/// disposable memo tables. Off by default until full correctness/resource gates.
pub(crate) fn reclamation_enabled() -> bool {
    thread_local! {
        static ENABLED: bool = std::env::var_os("KIOTA_RECLAIM").is_some();
    }
    ENABLED.with(|enabled| *enabled)
}

pub(crate) fn memo_insert<K: Eq + Hash, V>(memo: &mut FxHashMap<K, V>, key: K, value: V) {
    if reclamation_enabled() && memo.len() >= 50_000 {
        memo.clear();
    }
    memo.insert(key, value);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    Nat(num_bigint::BigUint),
    Str(Rc<String>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    BVar(u32),
    Sort(Level),
    Const(u32, Rc<Vec<Level>>), // name index, universe args
    App(Expr, Expr),
    Lam(BinderInfo, Expr, Expr), // type, body
    Pi(BinderInfo, Expr, Expr),  // type, body
    Let(Expr, Expr, Expr),       // type, value, body
    Proj(u32, u32, Expr),        // struct name index, field index, struct value
    Lit(Lit),
}

/// An interned node plus the facts hot paths need constantly.
///
/// `loose` is the smallest `k` such that every loose bvar has index `< k`
/// (0 = closed). `used_bvars` is the bitset of those indices (`bit i` = bvar
/// `i` occurs); `u64::MAX` means some bvar is `≥ 64` and the defeq pair key
/// must fall back to `suffix[loose]`.
pub struct ExprNode {
    identity: usize,
    data: ExprData,
    loose: u32,
    used_bvars: u64,
}

impl std::ops::Deref for ExprNode {
    type Target = ExprData;
    #[inline(always)]
    fn deref(&self) -> &ExprData {
        &self.data
    }
}

impl std::fmt::Debug for ExprNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

// Every node is created through `intern`, which returns the existing
// allocation for a structurally equal node. So identity is address equality,
// and that is already the invariant `node_eq` relies on for children.
impl PartialEq for ExprNode {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for ExprNode {}
impl Hash for ExprNode {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state)
    }
}

// Interned terms form spines that can be thousands of nodes deep (e.g. a
// left-nested `App` chain). The compiler-derived recursive drop would recurse
// once per spine node and overflow the stack, so a node whose release can
// cascade dismantles its children with a heap worklist: teardown depth is
// O(1) regardless of term depth.
//
// Most releases cannot cascade. The hash-cons table holds a reference to
// every node it knows, so when a table reset walks the slots nearly every
// child of a dying node is still referenced from somewhere else. When every
// child is, dropping the fields only decrements counters, and the worklist
// (and its allocation) is skipped.
impl Drop for ExprNode {
    #[inline]
    fn drop(&mut self) {
        // Whether releasing this node's reference could be the child's last.
        #[inline(always)]
        fn last(e: &Expr) -> bool {
            Rc::strong_count(e) == 1
        }
        let cascades = match &self.data {
            ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {
                false
            }
            // The same child twice holds two of its references: both go.
            ExprData::App(a, b) | ExprData::Lam(_, a, b) | ExprData::Pi(_, a, b) => {
                last(a) || last(b) || Rc::ptr_eq(a, b)
            }
            ExprData::Let(a, b, c) => {
                last(a)
                    || last(b)
                    || last(c)
                    || Rc::ptr_eq(a, b)
                    || Rc::ptr_eq(a, c)
                    || Rc::ptr_eq(b, c)
            }
            ExprData::Proj(_, _, v) => last(v),
        };
        if cascades {
            drop_cascade(&mut self.data);
        }
    }
}

thread_local! {
    /// The worklist `drop_cascade` reuses, so a cascade does not allocate.
    static DROP_STACK: RefCell<Vec<Expr>> = const { RefCell::new(Vec::new()) };
}

/// A worklist that grew past this many entries is freed instead of kept.
const DROP_STACK_KEEP: usize = 1 << 16;

#[inline(never)]
fn drop_cascade(data: &mut ExprData) {
    // `try_with`: a node can die while the thread's locals are being torn
    // down, after this one is gone. A worklist dropped mid-use (it is taken
    // out of the cell, so nothing here observes that) is only an allocation.
    let mut stack: Vec<Expr> = DROP_STACK
        .try_with(|s| std::mem::take(&mut *s.borrow_mut()))
        .unwrap_or_default();
    take_children(data, &mut stack);
    while let Some(e) = stack.pop() {
        if let Ok(mut node) = Rc::try_unwrap(e) {
            take_children(&mut node.data, &mut stack);
            // `node` drops here childless: its own `drop` returns at once.
        }
    }
    if stack.capacity() <= DROP_STACK_KEEP {
        let _ = DROP_STACK.try_with(|s| *s.borrow_mut() = stack);
    }
}

/// Move any `Expr` children out of `d`, leaving a childless placeholder, so the
/// caller can drop them iteratively instead of recursively.
fn take_children(d: &mut ExprData, out: &mut Vec<Expr>) {
    match std::mem::replace(d, ExprData::BVar(0)) {
        ExprData::App(f, a) => {
            out.push(f);
            out.push(a);
        }
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            out.push(ty);
            out.push(body);
        }
        ExprData::Let(ty, val, body) => {
            out.push(ty);
            out.push(val);
            out.push(body);
        }
        ExprData::Proj(_, _, v) => out.push(v),
        ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {}
    }
}

pub type Expr = Rc<ExprNode>;

fn ptr(e: &Expr) -> usize {
    identity(e)
}

/// Exact allocation identity that is never reused, even after interner resets.
/// Address reuse must not let a memo entry for a discarded term match a new
/// allocation. IDs are thread-local, like the Rc terms and all checker caches.
pub fn identity(e: &Expr) -> usize {
    e.identity
}

/// The smallest `k` such that every loose bvar in `e` has index `< k`.
/// Zero means `e` is closed.
///
/// This is the quantity that makes eager substitution affordable: a subterm
/// whose range is `<= depth` cannot be touched by a substitution at `depth`,
/// so `instantiate`/`shift` can return it whole instead of rebuilding it.
#[inline(always)]
pub fn loose_bvar_range(e: &Expr) -> u32 {
    e.loose
}

/// Bitset of loose bvar indices, or `u64::MAX` if some index is `≥ 64`.
#[inline(always)]
pub fn used_bvars(e: &Expr) -> u64 {
    e.used_bvars
}

const USED_OVERFLOW: u64 = u64::MAX;

fn used_or(a: u64, b: u64) -> u64 {
    if a == USED_OVERFLOW || b == USED_OVERFLOW {
        USED_OVERFLOW
    } else {
        a | b
    }
}

fn used_shift_binder(u: u64) -> u64 {
    if u == USED_OVERFLOW {
        USED_OVERFLOW
    } else {
        u >> 1
    }
}

/// Computed once per node from children that already carry their own bits.
fn used_of(d: &ExprData) -> u64 {
    match d {
        ExprData::BVar(i) => {
            if *i >= 64 {
                USED_OVERFLOW
            } else {
                1u64 << *i
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => 0,
        ExprData::App(f, a) => used_or(f.used_bvars, a.used_bvars),
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            used_or(ty.used_bvars, used_shift_binder(body.used_bvars))
        }
        ExprData::Let(ty, val, body) => used_or(
            used_or(ty.used_bvars, val.used_bvars),
            used_shift_binder(body.used_bvars),
        ),
        ExprData::Proj(_, _, v) => v.used_bvars,
    }
}

/// Computed once per node, from children that already carry their own range.
fn loose_of(d: &ExprData) -> u32 {
    match d {
        ExprData::BVar(i) => *i + 1,
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => 0,
        ExprData::App(f, a) => f.loose.max(a.loose),
        ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
            ty.loose.max(body.loose.saturating_sub(1))
        }
        ExprData::Let(ty, val, body) => ty.loose.max(val.loose).max(body.loose.saturating_sub(1)),
        ExprData::Proj(_, _, v) => v.loose,
    }
}

/// Odd multiplier (the one `rustc-hash` 2 uses). A multiply pushes entropy
/// toward the high bits, which is where the table takes its index from.
const HASH_K: u64 = 0xf135_7aea_2e62_a9c5;

/// Fold `x` into `h`. The half-rotation brings the well-mixed high half of
/// the previous product down, so the next multiply spreads both words again.
/// For two words under 2^32 (node identities) the 64-bit result is injective.
#[inline(always)]
fn hash_mix(h: u64, x: u64) -> u64 {
    (h.rotate_left(32) ^ x).wrapping_mul(HASH_K)
}

// One arbitrary odd seed per node kind, so equal children under different
// kinds do not collide systematically.
const SEED_BVAR: u64 = 0x9e37_79b9_7f4a_7c15;
const SEED_SORT: u64 = 0xc2b2_ae3d_27d4_eb4f;
const SEED_CONST: u64 = 0x1656_67b1_9e37_79f9;
const SEED_APP: u64 = 0x27d4_eb2f_1656_67c5;
const SEED_LAM: u64 = 0x85eb_ca77_c2b2_ae63;
const SEED_PI: u64 = 0xff51_afd7_ed55_8ccd;
const SEED_LET: u64 = 0xc4ce_b9fe_1a85_ec53;
const SEED_PROJ: u64 = 0x2545_f491_4f6c_dd1d;
const SEED_NAT: u64 = 0x94d0_49bb_1331_11eb;
const SEED_STR: u64 = 0xbf58_476d_1ce4_e5b9;

/// Structural hash of one node. Children contribute their identity, never
/// their content, so the cost does not depend on term size. Only the lookup
/// structure reads this value: every candidate is confirmed by `node_eq`,
/// so the function is free to change without changing any result.
#[inline]
fn hash_node(d: &ExprData) -> u64 {
    match d {
        ExprData::BVar(i) => hash_mix(SEED_BVAR, *i as u64),
        ExprData::Sort(l) => {
            let mut h = FxHasher::default();
            l.hash(&mut h);
            hash_mix(SEED_SORT, h.finish())
        }
        ExprData::Const(n, us) => {
            let mut h = FxHasher::default();
            n.hash(&mut h);
            us.hash(&mut h);
            hash_mix(SEED_CONST, h.finish())
        }
        ExprData::App(f, a) => hash_mix(hash_mix(SEED_APP, ptr(f) as u64), ptr(a) as u64),
        ExprData::Lam(bi, ty, body) => hash_mix(
            hash_mix(SEED_LAM.wrapping_add(*bi as u64), ptr(ty) as u64),
            ptr(body) as u64,
        ),
        ExprData::Pi(bi, ty, body) => hash_mix(
            hash_mix(SEED_PI.wrapping_add(*bi as u64), ptr(ty) as u64),
            ptr(body) as u64,
        ),
        ExprData::Let(ty, val, body) => hash_mix(
            hash_mix(hash_mix(SEED_LET, ptr(ty) as u64), ptr(val) as u64),
            ptr(body) as u64,
        ),
        ExprData::Proj(s, i, v) => hash_mix(
            hash_mix(SEED_PROJ, ((*s as u64) << 32) | *i as u64),
            ptr(v) as u64,
        ),
        ExprData::Lit(Lit::Nat(n)) => {
            let mut h = FxHasher::default();
            n.hash(&mut h);
            hash_mix(SEED_NAT, h.finish())
        }
        ExprData::Lit(Lit::Str(s)) => {
            let mut h = FxHasher::default();
            s.hash(&mut h);
            hash_mix(SEED_STR, h.finish())
        }
    }
}

fn node_eq(a: &ExprData, b: &ExprData) -> bool {
    match (a, b) {
        (ExprData::BVar(i), ExprData::BVar(j)) => i == j,
        (ExprData::Sort(x), ExprData::Sort(y)) => x == y,
        (ExprData::Const(n1, u1), ExprData::Const(n2, u2)) => n1 == n2 && u1 == u2,
        (ExprData::App(f1, a1), ExprData::App(f2, a2)) => Rc::ptr_eq(f1, f2) && Rc::ptr_eq(a1, a2),
        (ExprData::Lam(b1, t1, x1), ExprData::Lam(b2, t2, x2)) => {
            b1 == b2 && Rc::ptr_eq(t1, t2) && Rc::ptr_eq(x1, x2)
        }
        (ExprData::Pi(b1, t1, x1), ExprData::Pi(b2, t2, x2)) => {
            b1 == b2 && Rc::ptr_eq(t1, t2) && Rc::ptr_eq(x1, x2)
        }
        (ExprData::Let(t1, v1, b1), ExprData::Let(t2, v2, b2)) => {
            Rc::ptr_eq(t1, t2) && Rc::ptr_eq(v1, v2) && Rc::ptr_eq(b1, b2)
        }
        (ExprData::Proj(s1, i1, v1), ExprData::Proj(s2, i2, v2)) => {
            s1 == s2 && i1 == i2 && Rc::ptr_eq(v1, v2)
        }
        (ExprData::Lit(x), ExprData::Lit(y)) => x == y,
        _ => false,
    }
}

/// One table slot: the node and the hash it was filed under. Keeping the
/// hash beside the pointer lets a probe skip a mismatched neighbour, and lets
/// the table grow, without touching the node itself.
#[derive(Clone)]
struct Slot {
    hash: u64,
    node: Option<Expr>,
}

const EMPTY_SLOT: Slot = Slot { hash: 0, node: None };

/// Slots a new table starts with (1 MiB). Small inputs stay cache-resident.
const INITIAL_SLOTS_LOG2: u32 = 16;
/// A table reset keeps its slots up to this size (256 MiB) and shrinks a
/// larger one, so one outsized declaration does not pin its table forever.
const RETAINED_SLOTS_LOG2: u32 = 24;

/// Hash-cons table: open addressing with linear probing over a power-of-two
/// slot array, indexed by the top bits of `hash_node`.
///
/// Nodes are never removed one at a time (only `clear` empties the table),
/// so there are no tombstones and a probe stops at the first empty slot.
/// A lookup costs one cache line of slots plus the candidate node, where
/// the `HashMap<u64, Expr>` it replaces paid a control-byte group, a bucket
/// and the node, and re-hashed its `u64` key. `clear` keeps the slot array,
/// so the table is not regrown (and its pages not re-faulted) after every
/// reset.
struct Interner {
    slots: Vec<Slot>,
    /// `64 - log2(slots.len())`: the index is the top bits of the hash.
    shift: u32,
    len: usize,
    /// Grow once `len` passes this (5/8 of the slots).
    grow_at: usize,
    /// `intern` calls on this thread, in either mode.
    calls: u64,
    /// The call count at which the next progress line is printed.
    next_report: u64,
    /// `KIOTA_RECLAIM`: this table stays empty and `WEAK_INTERN` files the
    /// nodes. Read once here so the hot path does not ask the environment's
    /// thread-local on every call.
    weak_mode: bool,
}

impl Default for Interner {
    fn default() -> Self {
        Interner::with_slots_log2(INITIAL_SLOTS_LOG2)
    }
}

impl Interner {
    fn with_slots_log2(log2: u32) -> Self {
        let n = 1usize << log2;
        Interner {
            slots: vec![EMPTY_SLOT; n],
            shift: 64 - log2,
            len: 0,
            grow_at: n / 8 * 5,
            calls: 0,
            next_report: INTERN_REPORT_EVERY,
            weak_mode: reclamation_enabled(),
        }
    }

    #[inline]
    fn intern(&mut self, d: ExprData) -> Expr {
        let h = hash_node(&d);
        let mask = self.slots.len() - 1;
        let mut i = (h >> self.shift) as usize;
        loop {
            let slot = &self.slots[i];
            match &slot.node {
                None => break,
                Some(e) => {
                    if slot.hash == h && node_eq(&d, e) {
                        return e.clone();
                    }
                }
            }
            i = (i + 1) & mask;
        }
        let e = alloc_node(d);
        self.slots[i] = Slot {
            hash: h,
            node: Some(e.clone()),
        };
        self.len += 1;
        if self.len > self.grow_at {
            self.grow();
        }
        e
    }

    /// Double the slot array. Re-filing uses the stored hash only.
    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        let log2 = 64 - self.shift + 1;
        let n = 1usize << log2;
        let old = std::mem::replace(&mut self.slots, vec![EMPTY_SLOT; n]);
        self.shift = 64 - log2;
        self.grow_at = n / 8 * 5;
        let mask = n - 1;
        for slot in old {
            if slot.node.is_some() {
                let mut i = (slot.hash >> self.shift) as usize;
                while self.slots[i].node.is_some() {
                    i = (i + 1) & mask;
                }
                self.slots[i] = slot;
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.len
    }

    /// Drop every node reference the table holds. The slot array is kept
    /// (unless it outgrew `RETAINED_SLOTS_LOG2`), so the refill neither
    /// re-allocates nor re-files anything.
    fn clear(&mut self) {
        if self.slots.len() > 1usize << RETAINED_SLOTS_LOG2 {
            let fresh = Interner::with_slots_log2(RETAINED_SLOTS_LOG2);
            let old = std::mem::replace(&mut self.slots, fresh.slots);
            self.shift = fresh.shift;
            self.grow_at = fresh.grow_at;
            drop(old);
        } else if self.len != 0 {
            for slot in self.slots.iter_mut() {
                slot.node = None;
            }
        }
        self.len = 0;
    }
}

fn alloc_node(d: ExprData) -> Expr {
    let loose = loose_of(&d);
    let used_bvars = used_of(&d);
    Rc::new(ExprNode {
        identity: NEXT_NODE_ID.with(|next| {
            let id = next.get();
            next.set(id.checked_add(1).expect("expression identity exhausted"));
            id
        }),
        data: d,
        loose,
        used_bvars,
    })
}

thread_local! {
    static NEXT_NODE_ID: std::cell::Cell<usize> = const { std::cell::Cell::new(1) };
    static INTERN: RefCell<Interner> = RefCell::new(Interner::default());
    static WEAK_INTERN: RefCell<reclaim::WeakInterner> = RefCell::new(reclaim::WeakInterner::default());
    static LEVEL_INST_MEMO: RefCell<FxHashMap<(usize, usize), Expr>> =
        RefCell::new(FxHashMap::default());
    // IDs are assigned only after comparing the complete substitution. A hash
    // collision must never identify two different universe instantiations.
    static LEVEL_SUBST_IDS: RefCell<FxHashMap<Vec<(u32, Level)>, usize>> =
        RefCell::new(FxHashMap::default());
    static SHIFT_MEMO: RefCell<FxHashMap<(usize, i32, u32), Expr>> =
        RefCell::new(FxHashMap::default());
    static INST1_MEMO: RefCell<FxHashMap<(usize, usize), Expr>> =
        RefCell::new(FxHashMap::default());
    /// Node → sorted list of its loose bvar indices (see `used_bvar_set`),
    /// `None` once a list would pass `USED_SET_CAP` entries.
    static USED_SET_MEMO: RefCell<FxHashMap<usize, Option<Rc<[u32]>>>> =
        RefCell::new(FxHashMap::default());
}

/// Most entries an occurrence list may have. A term that mentions more
/// binders than this keys on the whole telescope, as every overflowed term
/// did before; the list is for the common deep-context term that mentions
/// a few binders far out.
pub const USED_SET_CAP: usize = 64;

/// The loose bvar indices of `e`, sorted ascending, for a term whose
/// one-word `used_bvars` summary overflowed. The summary cannot tell *which*
/// indices a term under 64 or more binders uses, and a context key that
/// falls back to the whole telescope then differs for every binder pushed,
/// so nothing computed about the term is ever found again.
///
/// `None` when `e` mentions more than `USED_SET_CAP` binders. Computed once
/// per node from its children's lists (a binder shifts the body's indices
/// down by one and drops index 0), memoized for the current declaration
/// (`clear_subst_memos`). Keying the memo on the node alone is what keeps
/// a nest of thousands of binders linear; a memo keyed on the node and the
/// depth it is seen at is quadratic there.
pub fn used_bvar_set(e: &Expr) -> Option<Rc<[u32]>> {
    if e.used_bvars != USED_OVERFLOW {
        return Some(Rc::from(bits_to_list(e.used_bvars, 0)));
    }
    let id = identity(e);
    if let Some(r) = USED_SET_MEMO.with(|m| m.borrow().get(&id).cloned()) {
        return r;
    }
    let r: Option<Rc<[u32]>> = (|| {
        let mut acc: Vec<u32> = Vec::new();
        match &e.data {
            ExprData::BVar(i) => acc.push(*i),
            ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {}
            ExprData::App(f, a) => {
                merge_used(&mut acc, &child_used(f, 0)?)?;
                merge_used(&mut acc, &child_used(a, 0)?)?;
            }
            ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
                merge_used(&mut acc, &child_used(ty, 0)?)?;
                merge_used(&mut acc, &child_used(body, 1)?)?;
            }
            ExprData::Let(ty, val, body) => {
                merge_used(&mut acc, &child_used(ty, 0)?)?;
                merge_used(&mut acc, &child_used(val, 0)?)?;
                merge_used(&mut acc, &child_used(body, 1)?)?;
            }
            ExprData::Proj(_, _, v) => merge_used(&mut acc, &child_used(v, 0)?)?,
        }
        Some(Rc::from(acc))
    })();
    USED_SET_MEMO.with(|m| m.borrow_mut().insert(id, r.clone()));
    r
}

/// The indices of `c` at or above `drop`, re-based to `drop`.
fn child_used(c: &Expr, drop: u32) -> Option<Vec<u32>> {
    if c.loose <= drop {
        return Some(Vec::new());
    }
    if c.used_bvars != USED_OVERFLOW {
        // `loose <= 64` with `loose > drop` keeps the shift in range.
        return Some(bits_to_list(c.used_bvars >> drop, 0));
    }
    let set = used_bvar_set(c)?;
    Some(set.iter().filter(|&&i| i >= drop).map(|&i| i - drop).collect())
}

/// Sorted union into `acc`; `None` once the result passes the cap.
fn merge_used(acc: &mut Vec<u32>, other: &[u32]) -> Option<()> {
    if other.is_empty() {
        return Some(());
    }
    let mut merged = Vec::with_capacity(acc.len() + other.len());
    let (mut i, mut j) = (0, 0);
    while i < acc.len() || j < other.len() {
        let next = match (acc.get(i), other.get(j)) {
            (Some(a), Some(b)) if a < b => { i += 1; *a }
            (Some(a), Some(b)) if a > b => { j += 1; *b }
            (Some(a), Some(_)) => { i += 1; j += 1; *a }
            (Some(a), None) => { i += 1; *a }
            (None, Some(b)) => { j += 1; *b }
            (None, None) => unreachable!(),
        };
        merged.push(next);
        if merged.len() > USED_SET_CAP {
            return None;
        }
    }
    *acc = merged;
    Some(())
}

/// The set bits of a one-word summary as indices, each plus `base`.
pub fn bits_to_list(mut bits: u64, base: u32) -> Vec<u32> {
    let mut out = Vec::with_capacity(bits.count_ones() as usize);
    while bits != 0 {
        let i = bits.trailing_zeros();
        out.push(i + base);
        bits &= bits - 1;
    }
    out
}

/// A progress line on stderr every this many `intern` calls.
const INTERN_REPORT_EVERY: u64 = 100_000_000;

pub fn intern(d: ExprData) -> Expr {
    INTERN.with(|t| {
        let mut t = t.borrow_mut();
        t.calls += 1;
        if t.calls == t.next_report {
            t.next_report += INTERN_REPORT_EVERY;
            let n = t.calls;
            let nodes = if t.weak_mode {
                WEAK_INTERN.with(|w| w.borrow().len())
            } else {
                t.len()
            };
            eprintln!("INTERN_CALLS {n} nodes={nodes}");
            let _ = std::io::Write::flush(&mut std::io::stderr());
        }
        if t.weak_mode {
            drop(t);
            WEAK_INTERN.with(|t| t.borrow_mut().intern(d))
        } else {
            t.intern(d)
        }
    })
}

pub fn intern_node_count() -> usize {
    if reclamation_enabled() {
        WEAK_INTERN.with(|t| t.borrow().len())
    } else {
        INTERN.with(|t| t.borrow().len())
    }
}

/// Drop the hash-cons table's own lookup structure if it has grown past
/// `threshold` nodes, returning whether it did. The lookup key is a
/// structural hash of the node's content, not an address, so a miss
/// after clearing just re-allocates an equal node — it cannot return a
/// wrong one. Callers must drop every pointer-keyed cache *and* every
/// map that holds a strong `Rc` into interned terms (`unfold_cache`,
/// `iota_value_cache`, `iota_lit_memo`) *before* this runs: those maps
/// otherwise pin the pre-clear generation, and `iota_lit_memo` keys on
/// raw `usize` addresses that the allocator may reuse. A large finite
/// threshold (well above Init, Std, or any existing fixture) keeps
/// ordinary runs byte-for-byte unaffected. Cedar-scale exports hit it
/// when the table's next capacity-doubling (~24M nodes → ~3.3 GB) is
/// larger than one affordable allocation.
pub fn intern_clear_if_large(threshold: usize) -> bool {
    if reclamation_enabled() {
        return WEAK_INTERN.with(|t| {
            let mut t = t.borrow_mut();
            if t.len() > threshold {
                *t = reclaim::WeakInterner::default();
                true
            } else {
                false
            }
        });
    }
    INTERN.with(|t| {
        let mut t = t.borrow_mut();
        if t.len() > threshold {
            t.clear();
            true
        } else {
            false
        }
    })
}

pub fn intern_calls() -> u64 {
    INTERN.with(|t| t.borrow().calls)
}

/// Allocate `n` unique interned apps so a later Check sees a large table
/// without typechecking 18k decls. `KIOTA_WARM_INTERN`.
pub fn warm_intern(n: u32) {
    let mut e = bvar(0);
    for i in 0..n {
        e = app(e, lit_nat(BigUint::from(i)));
    }
    let _ = e;
}

/// Drop per-decl substitution memos. The intern table stays: env terms
/// live there. These two maps grow with every `shift`/`instantiate_level_params`
/// and were never cleared, so std `#18000` hung after 18k decls of residue.
pub fn clear_subst_memos() {
    LEVEL_INST_MEMO.with(|m| m.borrow_mut().clear());
    // Clear the memo first: IDs can be reused only after its entries are gone.
    LEVEL_SUBST_IDS.with(|m| m.borrow_mut().clear());
    SHIFT_MEMO.with(|m| m.borrow_mut().clear());
    INST1_MEMO.with(|m| m.borrow_mut().clear());
    USED_SET_MEMO.with(|m| m.borrow_mut().clear());
}

pub fn bvar(i: u32) -> Expr {
    intern(ExprData::BVar(i))
}
pub fn sort(l: Level) -> Expr {
    intern(ExprData::Sort(l))
}
pub fn const_(n: u32, us: Vec<Level>) -> Expr {
    intern(ExprData::Const(n, Rc::new(us)))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    intern(ExprData::App(f, a))
}
pub fn lam(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    intern(ExprData::Lam(bi, ty, body))
}
pub fn pi(bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
    intern(ExprData::Pi(bi, ty, body))
}
pub fn let_(ty: Expr, val: Expr, body: Expr) -> Expr {
    intern(ExprData::Let(ty, val, body))
}
pub fn proj(s: u32, i: u32, e: Expr) -> Expr {
    intern(ExprData::Proj(s, i, e))
}
pub fn lit_nat(n: num_bigint::BigUint) -> Expr {
    intern(ExprData::Lit(Lit::Nat(n)))
}
pub fn lit_str(s: impl Into<String>) -> Expr {
    intern(ExprData::Lit(Lit::Str(Rc::new(s.into()))))
}

/// True when `e` has no loose bvars.
#[inline(always)]
pub fn is_closed(e: &Expr) -> bool {
    e.loose == 0
}

pub fn apps(f: Expr, args: &[Expr]) -> Expr {
    let mut r = f;
    for a in args {
        r = app(r, a.clone());
    }
    r
}

/// Shift free (>= cutoff) de Bruijn indices by `by` (can be used with negative
/// effectively only in controlled contexts; we only ever shift up here).
pub fn shift(e: &Expr, by: i32, cutoff: u32) -> Expr {
    if by == 0 {
        return e.clone();
    }
    // Every loose bvar is below the cutoff, so nothing here moves.
    if loose_bvar_range(e) <= cutoff {
        return e.clone();
    }
    let key = (ptr(e), by, cutoff);
    if let Some(r) = SHIFT_MEMO.with(|m| m.borrow().get(&key).cloned()) {
        return r;
    }
    crate::stats::shift_node();
    let r = match &***e {
        ExprData::BVar(i) => {
            if *i >= cutoff {
                bvar((*i as i64 + by as i64) as u32)
            } else {
                e.clone()
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
        ExprData::App(f, a) => app(shift(f, by, cutoff), shift(a, by, cutoff)),
        ExprData::Lam(bi, ty, body) => lam(*bi, shift(ty, by, cutoff), shift(body, by, cutoff + 1)),
        ExprData::Pi(bi, ty, body) => pi(*bi, shift(ty, by, cutoff), shift(body, by, cutoff + 1)),
        ExprData::Let(ty, val, body) => let_(
            shift(ty, by, cutoff),
            shift(val, by, cutoff),
            shift(body, by, cutoff + 1),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, shift(v, by, cutoff)),
    };
    SHIFT_MEMO.with(|m| {
        memo_insert(&mut m.borrow_mut(), key, r.clone());
    });
    r
}

/// Substitute `args` (in reverse: args[0] replaces the innermost bound var 0)
/// into `e`, which lives at binding depth `depth` (number of binders already
/// opened above the substitution site, i.e. args need to be shifted by `depth`
/// when they replace a bvar).
pub fn instantiate(e: &Expr, args: &[Expr]) -> Expr {
    // Proof bodies are DAG-shared through the interner: the same subterm
    // reaches many occurrences, and without a memo each occurrence pays a
    // full traversal. The grind perf tests amplify a shared simp-lemma
    // application thousands of times; keying on (node, depth) — args are
    // fixed within one call — visits each unique node once.
    //
    // The memo is per call, but its allocation is not: a fresh map grew
    // from nothing on every substitution (allocate, re-file, free, several
    // times over for a body of a few dozen nodes). The map is borrowed from
    // a thread-local and handed back empty, so the entries, the hits and
    // the misses of every call are exactly what a fresh map would give.
    if loose_bvar_range(e) == 0 {
        // What `instantiate_core` answers at depth 0, before any memo use.
        return e.clone();
    }
    let mut memo = INST_SCRATCH
        .try_with(|m| std::mem::take(&mut *m.borrow_mut()))
        .unwrap_or_default();
    let r = instantiate_core(e, args, 0, &mut memo);
    // Emptying a map costs its capacity, not its length, so a map one large
    // body stretched is dropped instead of being re-emptied by every small
    // substitution after it.
    if memo.capacity() <= INST_SCRATCH_KEEP {
        memo.clear();
        let _ = INST_SCRATCH.try_with(|m| *m.borrow_mut() = memo);
    }
    r
}

/// Largest capacity (entries) of the substitution memo that is kept for
/// the next `instantiate` call.
const INST_SCRATCH_KEEP: usize = 1 << 10;

thread_local! {
    /// The emptied memo of the last `instantiate` call, for its allocation.
    static INST_SCRATCH: RefCell<FxHashMap<(usize, u32), Expr>> =
        RefCell::new(FxHashMap::default());
}

fn instantiate_core(
    e: &Expr,
    args: &[Expr],
    depth: u32,
    memo: &mut rustc_hash::FxHashMap<(usize, u32), Expr>,
) -> Expr {
    // Every loose bvar is bound above `depth`, so neither the substitution nor
    // the renumbering below can reach into this subterm. Returning it whole is
    // what turns O(term size) per binder into O(path length).
    if loose_bvar_range(e) <= depth {
        return e.clone();
    }
    let key = (identity(e), depth);
    if let Some(r) = memo.get(&key) {
        return r.clone();
    }
    crate::stats::inst_node();
    let r = match &***e {
        ExprData::BVar(i) => {
            if *i >= depth && ((*i - depth) as usize) < args.len() {
                let a = &args[(*i - depth) as usize];
                shift(a, depth as i32, 0)
            } else if *i >= depth {
                bvar(*i - args.len() as u32)
            } else {
                e.clone()
            }
        }
        ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
        ExprData::App(f, a) => app(
            instantiate_core(f, args, depth, memo),
            instantiate_core(a, args, depth, memo),
        ),
        ExprData::Lam(bi, ty, body) => lam(
            *bi,
            instantiate_core(ty, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Pi(bi, ty, body) => pi(
            *bi,
            instantiate_core(ty, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Let(ty, val, body) => let_(
            instantiate_core(ty, args, depth, memo),
            instantiate_core(val, args, depth, memo),
            instantiate_core(body, args, depth + 1, memo),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_core(v, args, depth, memo)),
    };
    memo.insert(key, r.clone());
    r
}

/// Single-substitution convenience (beta / zeta): replace bvar 0 with `arg`.
pub fn instantiate1(e: &Expr, arg: &Expr) -> Expr {
    let key = (ptr(e), ptr(arg));
    if let Some(r) = INST1_MEMO.with(|m| m.borrow().get(&key).cloned()) {
        return r;
    }
    let r = instantiate(e, std::slice::from_ref(arg));
    INST1_MEMO.with(|m| {
        memo_insert(&mut m.borrow_mut(), key, r.clone());
    });
    r
}

/// Canonicalize once per public call, not once per expression node. The hash
/// table checks full key equality before reusing an ID, including collisions.
fn level_subst_id<S: std::hash::BuildHasher>(
    subst: &FxHashMap<u32, Level>,
    ids: &mut std::collections::HashMap<Vec<(u32, Level)>, usize, S>,
) -> usize {
    let mut key: Vec<_> = subst.iter().map(|(&n, l)| (n, l.clone())).collect();
    key.sort_unstable_by_key(|(n, _)| *n);
    let next = ids.len();
    *ids.entry(key).or_insert(next)
}

/// The first universe parameter `e` mentions that is not in `declared`.
/// `seen` carries the composite nodes already walked, so the fields of one
/// declaration share the work and a shared subterm is walked once.
pub fn undeclared_level_param(
    e: &Expr,
    declared: &[u32],
    seen: &mut rustc_hash::FxHashSet<usize>,
) -> Option<u32> {
    fn in_level(l: &Level, declared: &[u32]) -> Option<u32> {
        use crate::level::LevelData;
        let mut stack = vec![l];
        while let Some(l) = stack.pop() {
            match &**l {
                LevelData::Zero => {}
                LevelData::Param(p) => {
                    if !declared.contains(p) {
                        return Some(*p);
                    }
                }
                LevelData::Succ(a) => stack.push(a),
                LevelData::Max(a, b) | LevelData::IMax(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
            }
        }
        None
    }
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match &***e {
            ExprData::BVar(_) | ExprData::Lit(_) => {}
            ExprData::Sort(l) => {
                if let Some(p) = in_level(l, declared) {
                    return Some(p);
                }
            }
            ExprData::Const(_, ls) => {
                for l in ls.iter() {
                    if let Some(p) = in_level(l, declared) {
                        return Some(p);
                    }
                }
            }
            composite => {
                if !seen.insert(ptr(e)) {
                    continue;
                }
                match composite {
                    ExprData::App(f, a) => {
                        stack.push(f);
                        stack.push(a);
                    }
                    ExprData::Lam(_, ty, body) | ExprData::Pi(_, ty, body) => {
                        stack.push(ty);
                        stack.push(body);
                    }
                    ExprData::Let(ty, val, body) => {
                        stack.push(ty);
                        stack.push(val);
                        stack.push(body);
                    }
                    ExprData::Proj(_, _, v) => stack.push(v),
                    _ => unreachable!(),
                }
            }
        }
    }
    None
}

pub fn instantiate_level_params(e: &Expr, subst: &FxHashMap<u32, Level>) -> Expr {
    if subst.is_empty() {
        return e.clone();
    }
    let id = LEVEL_SUBST_IDS.with(|ids| level_subst_id(subst, &mut ids.borrow_mut()));
    instantiate_level_params_cached(e, subst, id)
}

fn instantiate_level_params_cached(e: &Expr, subst: &FxHashMap<u32, Level>, id: usize) -> Expr {
    let key = (ptr(e), id);
    if let Some(r) = LEVEL_INST_MEMO.with(|m| m.borrow().get(&key).cloned()) {
        return r;
    }
    let r = instantiate_level_params_go(e, subst, id);
    LEVEL_INST_MEMO.with(|m| {
        memo_insert(&mut m.borrow_mut(), key, r.clone());
    });
    r
}

fn instantiate_level_params_go(e: &Expr, subst: &FxHashMap<u32, Level>, id: usize) -> Expr {
    match &***e {
        ExprData::BVar(_) | ExprData::Lit(_) => e.clone(),
        ExprData::Sort(l) => sort(crate::level::instantiate(l, subst)),
        ExprData::Const(n, us) => const_(
            *n,
            us.iter()
                .map(|l| crate::level::instantiate(l, subst))
                .collect(),
        ),
        ExprData::App(f, a) => app(
            instantiate_level_params_cached(f, subst, id),
            instantiate_level_params_cached(a, subst, id),
        ),
        ExprData::Lam(bi, ty, body) => lam(
            *bi,
            instantiate_level_params_cached(ty, subst, id),
            instantiate_level_params_cached(body, subst, id),
        ),
        ExprData::Pi(bi, ty, body) => pi(
            *bi,
            instantiate_level_params_cached(ty, subst, id),
            instantiate_level_params_cached(body, subst, id),
        ),
        ExprData::Let(ty, val, body) => let_(
            instantiate_level_params_cached(ty, subst, id),
            instantiate_level_params_cached(val, subst, id),
            instantiate_level_params_cached(body, subst, id),
        ),
        ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_level_params_cached(v, subst, id)),
    }
}

/// Decompose `f a1 a2 ... an` into (f, [a1..an]) (args in application order).
pub fn unfold_apps(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    loop {
        match &**cur {
            ExprData::App(f, a) => {
                args.push(a.clone());
                cur = f.clone();
            }
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level;

    #[test]
    fn intern_reuses_pointer() {
        let a = bvar(0);
        let b = bvar(0);
        assert!(Rc::ptr_eq(&a, &b));
        let f = const_(1, vec![]);
        let t1 = app(f.clone(), a.clone());
        let t2 = app(f, b);
        assert!(Rc::ptr_eq(&t1, &t2));
        let n1 = lit_nat(7u32.into());
        let n2 = lit_nat(7u32.into());
        assert!(Rc::ptr_eq(&n1, &n2));
        assert!(!Rc::ptr_eq(&n1, &lit_nat(8u32.into())));
    }

    #[test]
    fn instantiate1_memo_returns_same_ptr() {
        let body = app(bvar(0), bvar(1));
        let arg = const_(3, vec![]);
        let a = instantiate1(&body, &arg);
        let b = instantiate1(&body, &arg);
        assert!(Rc::ptr_eq(&a, &b));
    }

    #[test]
    fn intern_primary_reuses_after_many_unique() {
        let mut acc = bvar(0);
        for i in 0..8_000u32 {
            acc = app(acc, lit_nat(BigUint::from(i)));
        }
        let mut acc2 = bvar(0);
        for i in 0..8_000u32 {
            acc2 = app(acc2, lit_nat(BigUint::from(i)));
        }
        assert!(
            Rc::ptr_eq(&acc, &acc2),
            "primary intern map must still hash-cons after thousands of unique nodes"
        );
    }

    /// The table starts at `1 << INITIAL_SLOTS_LOG2` slots and doubles.
    /// Every node filed before a doubling must still be found after it,
    /// and a second pass must not allocate.
    #[test]
    fn interner_growth_keeps_every_node_findable() {
        let n = (1u32 << INITIAL_SLOTS_LOG2) * 3;
        let head = const_(7, vec![]);
        let before = intern_node_count();
        let first: Vec<Expr> = (0..n)
            .map(|i| app(head.clone(), lit_nat(BigUint::from(i))))
            .collect();
        let after = intern_node_count();
        assert!(after - before >= n as usize, "unique nodes were filed");
        for (i, e) in first.iter().enumerate() {
            let again = app(head.clone(), lit_nat(BigUint::from(i as u32)));
            assert!(Rc::ptr_eq(e, &again), "node {i} lost after growth");
        }
        assert_eq!(intern_node_count(), after, "second pass allocated");
    }

    /// Kinds that share children must not be confused with one another,
    /// whatever the hash says: `node_eq` decides.
    #[test]
    fn interner_distinguishes_kinds_over_the_same_children() {
        let a = bvar(1);
        let b = bvar(2);
        let nodes = [
            app(a.clone(), b.clone()),
            app(b.clone(), a.clone()),
            lam(BinderInfo::Default, a.clone(), b.clone()),
            lam(BinderInfo::Implicit, a.clone(), b.clone()),
            pi(BinderInfo::Default, a.clone(), b.clone()),
            pi(BinderInfo::InstImplicit, a.clone(), b.clone()),
            let_(a.clone(), b.clone(), a.clone()),
            let_(a.clone(), a.clone(), b.clone()),
            proj(1, 2, a.clone()),
            proj(2, 1, a.clone()),
            proj(1, 2, b.clone()),
        ];
        for (i, x) in nodes.iter().enumerate() {
            for (j, y) in nodes.iter().enumerate() {
                assert_eq!(Rc::ptr_eq(x, y), i == j, "nodes {i} and {j}");
            }
        }
    }

    /// A reset empties the table in place. What it held and nothing else
    /// referenced is freed; what something else still holds survives with
    /// its content, and the table hash-conses the next generation.
    #[test]
    fn interner_reset_frees_unreferenced_nodes_and_keeps_referenced_ones() {
        let kept = app(const_(11, vec![]), lit_nat(BigUint::from(5u32)));
        let kept_weak = Rc::downgrade(&kept);
        let dead_weak = {
            let dead = app(const_(12, vec![]), lit_nat(BigUint::from(6u32)));
            Rc::downgrade(&dead)
        };
        // Under `KIOTA_RECLAIM` the table holds no node alive to begin with.
        assert_eq!(
            dead_weak.upgrade().is_some(),
            !reclamation_enabled(),
            "the strong table holds it"
        );
        assert!(intern_clear_if_large(0));
        assert_eq!(intern_node_count(), 0);
        assert!(dead_weak.upgrade().is_none(), "reset freed the unreferenced node");
        assert!(kept_weak.upgrade().is_some());
        match &**kept {
            ExprData::App(f, a) => {
                assert!(matches!(&***f, ExprData::Const(11, _)));
                assert!(matches!(&***a, ExprData::Lit(Lit::Nat(n)) if *n == BigUint::from(5u32)));
            }
            _ => panic!("kept node changed shape"),
        }
        let x = app(bvar(0), bvar(1));
        assert!(Rc::ptr_eq(&x, &app(bvar(0), bvar(1))));
    }

    /// Releasing a spine hundreds of thousands of nodes deep must not
    /// recurse once per node: test threads have a 2 MiB stack.
    #[test]
    fn dropping_deep_spines_does_not_overflow_the_stack() {
        const DEPTH: u32 = 400_000;
        // Left-nested applications.
        let mut spine = bvar(0);
        for i in 0..DEPTH {
            spine = app(spine, lit_nat(BigUint::from(i)));
        }
        // Nested binders, body-deep.
        let mut binders = bvar(0);
        for _ in 0..DEPTH {
            binders = lam(BinderInfo::Default, s0(), binders);
        }
        // The same child on both sides: each level holds two references to
        // the level below, and nothing else does once the table lets go.
        let mut doubled = bvar(0);
        for _ in 0..DEPTH {
            doubled = app(doubled.clone(), doubled);
        }
        // Three references to the level below.
        let mut tripled = bvar(1);
        for _ in 0..DEPTH {
            tripled = let_(tripled.clone(), tripled.clone(), tripled);
        }
        let mut projs = bvar(2);
        for i in 0..DEPTH {
            projs = proj(i, 0, projs);
        }
        // With the table emptied these five are the only owners.
        assert!(intern_clear_if_large(0));
        let weak = [
            Rc::downgrade(&spine),
            Rc::downgrade(&binders),
            Rc::downgrade(&doubled),
            Rc::downgrade(&tripled),
            Rc::downgrade(&projs),
        ];
        drop((spine, binders, doubled, tripled, projs));
        assert!(weak.iter().all(|w| w.upgrade().is_none()));
    }

    /// The other order: the owners go first, so the table reset is what
    /// releases every node, in slot order rather than term order.
    #[test]
    fn resetting_a_table_of_deep_spines_does_not_overflow_the_stack() {
        const DEPTH: u32 = 400_000;
        let mut spine = bvar(0);
        let mut doubled = bvar(1);
        for i in 0..DEPTH {
            spine = app(spine, lit_nat(BigUint::from(i)));
            doubled = app(doubled.clone(), doubled);
        }
        let weak = [Rc::downgrade(&spine), Rc::downgrade(&doubled)];
        drop((spine, doubled));
        if reclamation_enabled() {
            // The weak table never owned them: the drop above released both.
            assert!(weak.iter().all(|w| w.upgrade().is_none()));
            return;
        }
        assert!(weak.iter().all(|w| w.upgrade().is_some()), "the table holds them");
        assert!(intern_clear_if_large(0));
        assert!(weak.iter().all(|w| w.upgrade().is_none()));
        assert_eq!(intern_node_count(), 0);
    }

    #[test]
    fn intern_clear_if_large_is_a_noop_under_threshold() {
        let _ = const_(1, vec![]);
        let n = intern_node_count();
        assert!(!intern_clear_if_large(n.saturating_add(1)));
        assert_eq!(intern_node_count(), n);
    }

    #[test]
    fn intern_clear_if_large_resets_table_and_still_hash_conses() {
        let mut acc = bvar(0);
        for i in 0..200u32 {
            acc = app(acc, lit_nat(BigUint::from(i)));
        }
        let n = intern_node_count();
        assert!(n > 50, "setup interned {n} nodes");
        assert!(intern_clear_if_large(50));
        assert_eq!(intern_node_count(), 0, "table itself is empty after reset");
        let a = bvar(0);
        let b = bvar(0);
        assert!(Rc::ptr_eq(&a, &b), "post-clear intern must still hash-cons");
        let _ = acc;
    }

    #[test]
    fn expression_identity_is_exact_and_never_reused_after_reset() {
        let first = const_(91, vec![]);
        let original_id = identity(&first);
        assert_eq!(original_id, identity(&const_(91, vec![])));
        clear_subst_memos();
        assert!(intern_clear_if_large(0));
        let second = const_(91, vec![]);
        assert_ne!(original_id, identity(&second));
        drop(first);
        drop(second);
        assert!(intern_clear_if_large(0));
        for n in 0..1_000 {
            assert!(identity(&const_(n, vec![])) > original_id);
        }
    }

    #[test]
    fn bvar_occurrence_uses_index_after_intern_reset() {
        // `elim_only_at_universe_zero` used to ask `args.iter().any(|a| **a ==
        // *expr::bvar(i))`. `ExprNode::eq` is pointer identity. After
        // `intern_clear_if_large`, env constructor terms still hold the old
        // `BVar(i)` node while a fresh `bvar(i)` is a new allocation, so an
        // Eq-shaped Prop inductive (data field occurring as a conclusion
        // index) was false-restricted.
        let args = vec![bvar(7), const_(1, vec![]), bvar(2)];
        let old = args[2].clone();
        assert!(intern_clear_if_large(0));
        let expected = bvar(2);
        assert!(
            !Rc::ptr_eq(&old, &expected),
            "reset must allocate a new intern node for BVar(2)"
        );
        assert!(
            !args.iter().any(|a| **a == *expected),
            "pointer equality is the intern-reset trap"
        );
        let want = 2u32;
        assert!(
            args.iter()
                .any(|a| matches!(&***a, ExprData::BVar(i) if *i == want)),
            "structural bvar index still finds the field in the conclusion"
        );
    }

    #[test]
    fn closed_detects_loose_bvars() {
        assert!(is_closed(&const_(1, vec![])));
        assert!(is_closed(&lit_nat(0u32.into())));
        assert!(is_closed(&sort(level::zero())));
        assert!(!is_closed(&bvar(0)));
        assert!(is_closed(&lam(
            BinderInfo::Default,
            sort(level::zero()),
            bvar(0)
        )));
        assert!(!is_closed(&lam(
            BinderInfo::Default,
            sort(level::zero()),
            bvar(1)
        )));
        assert!(is_closed(&app(
            lam(BinderInfo::Default, sort(level::zero()), bvar(0)),
            const_(1, vec![])
        )));
    }

    fn s0() -> Expr {
        sort(level::zero())
    }

    /// `used_bvars` is a one-word summary; past index 63 it only says
    /// "overflowed". `used_bvar_set` lists the indices, under binders too,
    /// until a term mentions more binders than `USED_SET_CAP`.
    #[test]
    fn used_bvar_set_lists_indices_past_64_binders_up_to_the_cap() {
        let list = |e: &Expr| used_bvar_set(e).map(|s| s.to_vec());
        let e = app(app(bvar(130), bvar(64)), bvar(0));
        assert_eq!(used_bvars(&e), u64::MAX, "the summary overflowed");
        assert_eq!(list(&e), Some(vec![0, 64, 130]));
        // One binder shifts every index down and drops the bound one.
        let under = lam(BinderInfo::Default, bvar(70), e.clone());
        assert_eq!(list(&under), Some(vec![63, 70, 129]));
        // A closed body under a binder contributes nothing; the domain does.
        let dom_only = pi(BinderInfo::Default, bvar(65), s0());
        assert_eq!(list(&dom_only), Some(vec![65]));
        // Mixed: an exact (small) child and an overflowed child.
        let mixed = let_(bvar(3), bvar(0), app(bvar(1), bvar(99)));
        assert_eq!(list(&mixed), Some(vec![0, 3, 98]));
        assert_eq!(loose_bvar_range(&mixed), 99);
        // Memoized per node: the same answer on a second call.
        assert_eq!(list(&e), Some(vec![0, 64, 130]));
        // A one-word term still answers, as a list.
        assert_eq!(list(&app(bvar(5), bvar(2))), Some(vec![2, 5]));
        // Past the cap the list is `None`, and so is every term built on it.
        let mut dense = bvar(64);
        for i in 65..(65 + USED_SET_CAP as u32) {
            dense = app(dense, bvar(i));
        }
        assert_eq!(used_bvar_set(&dense), None, "65 indices");
        assert_eq!(used_bvar_set(&app(dense.clone(), bvar(0))), None);
        assert_eq!(used_bvar_set(&lam(BinderInfo::Default, s0(), dense)), None);
        // Exactly the cap is still a list.
        let mut full = bvar(64);
        for i in 65..(64 + USED_SET_CAP as u32) {
            full = app(full, bvar(i));
        }
        assert_eq!(used_bvar_set(&full).map(|s| s.len()), Some(USED_SET_CAP));
    }

    #[test]
    fn loose_range_counts_the_highest_free_index() {
        assert_eq!(loose_bvar_range(&bvar(0)), 1);
        assert_eq!(loose_bvar_range(&bvar(3)), 4);
        assert_eq!(loose_bvar_range(&const_(1, vec![])), 0);
        // A binder discharges exactly one level.
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, s0(), bvar(0))),
            0
        );
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, s0(), bvar(2))),
            2
        );
        // The binder does not cover the domain, only the body.
        assert_eq!(
            loose_bvar_range(&lam(BinderInfo::Default, bvar(4), bvar(0))),
            5
        );
        assert_eq!(
            loose_bvar_range(&app(bvar(1), bvar(6))),
            7,
            "app takes the max of both sides"
        );
        assert_eq!(
            loose_bvar_range(&let_(bvar(2), bvar(1), bvar(3))),
            3,
            "only the let body is under the binder"
        );
        assert_eq!(loose_bvar_range(&proj(0, 0, bvar(5))), 6);
    }

    /// Reference substitution with no short-circuit, used to prove the fast
    /// path in `instantiate_core` never changes a result.
    fn instantiate_ref(e: &Expr, args: &[Expr], depth: u32) -> Expr {
        match &***e {
            ExprData::BVar(i) => {
                if *i >= depth && ((*i - depth) as usize) < args.len() {
                    shift_ref(&args[(*i - depth) as usize], depth as i32, 0)
                } else if *i >= depth {
                    bvar(*i - args.len() as u32)
                } else {
                    e.clone()
                }
            }
            ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
            ExprData::App(f, a) => app(
                instantiate_ref(f, args, depth),
                instantiate_ref(a, args, depth),
            ),
            ExprData::Lam(bi, ty, b) => lam(
                *bi,
                instantiate_ref(ty, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Pi(bi, ty, b) => pi(
                *bi,
                instantiate_ref(ty, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Let(ty, v, b) => let_(
                instantiate_ref(ty, args, depth),
                instantiate_ref(v, args, depth),
                instantiate_ref(b, args, depth + 1),
            ),
            ExprData::Proj(s, i, v) => proj(*s, *i, instantiate_ref(v, args, depth)),
        }
    }

    fn shift_ref(e: &Expr, by: i32, cutoff: u32) -> Expr {
        if by == 0 {
            return e.clone();
        }
        match &***e {
            ExprData::BVar(i) => {
                if *i >= cutoff {
                    bvar((*i as i64 + by as i64) as u32)
                } else {
                    e.clone()
                }
            }
            ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e.clone(),
            ExprData::App(f, a) => app(shift_ref(f, by, cutoff), shift_ref(a, by, cutoff)),
            ExprData::Lam(bi, ty, b) => {
                lam(*bi, shift_ref(ty, by, cutoff), shift_ref(b, by, cutoff + 1))
            }
            ExprData::Pi(bi, ty, b) => {
                pi(*bi, shift_ref(ty, by, cutoff), shift_ref(b, by, cutoff + 1))
            }
            ExprData::Let(ty, v, b) => let_(
                shift_ref(ty, by, cutoff),
                shift_ref(v, by, cutoff),
                shift_ref(b, by, cutoff + 1),
            ),
            ExprData::Proj(s, i, v) => proj(*s, *i, shift_ref(v, by, cutoff)),
        }
    }

    /// Deterministic pseudo-random terms over a small alphabet, deep enough to
    /// exercise nested binders and every node kind.
    fn gen(seed: &mut u64, depth: u32) -> Expr {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = (*seed >> 33) % if depth == 0 { 3 } else { 8 };
        match pick {
            0 => bvar((*seed >> 13) as u32 % 6),
            1 => const_((*seed >> 17) as u32 % 3, vec![]),
            2 => s0(),
            3 => app(gen(seed, depth - 1), gen(seed, depth - 1)),
            4 => lam(
                BinderInfo::Default,
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            5 => pi(
                BinderInfo::Default,
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            6 => let_(
                gen(seed, depth - 1),
                gen(seed, depth - 1),
                gen(seed, depth - 1),
            ),
            _ => proj(0, 0, gen(seed, depth - 1)),
        }
    }

    /// `instantiate` borrows its memo's allocation from the previous call.
    /// Whatever the previous call left behind (small, large enough to be
    /// dropped, or nothing), every call must answer as a fresh memo would.
    #[test]
    fn instantiate_memo_reuse_never_changes_substitution() {
        let mut seed = 0xD1CE_5EED_u64;
        // A body with far more distinct open nodes than the kept capacity.
        let mut wide = bvar(0);
        for i in 0..(4 * INST_SCRATCH_KEEP as u32) {
            wide = app(wide, app(bvar(1), lit_nat(BigUint::from(i))));
        }
        let a0 = const_(5, vec![]);
        let a1 = lam(BinderInfo::Default, s0(), bvar(0));
        for round in 0..60 {
            let e = gen(&mut seed, 5);
            let x = gen(&mut seed, 2);
            for args in [vec![x.clone()], vec![x.clone(), a1.clone()]] {
                assert!(
                    Rc::ptr_eq(&instantiate(&e, &args), &instantiate_ref(&e, &args, 0)),
                    "round {round}: reused memo changed a result"
                );
            }
            if round % 7 == 0 {
                // Stretch the memo past what is kept, then carry on.
                let args = [a0.clone(), a1.clone()];
                assert!(Rc::ptr_eq(
                    &instantiate(&wide, &args),
                    &instantiate_ref(&wide, &args, 0)
                ));
            }
            // A closed term comes back as itself, whatever the arguments.
            let closed = lam(BinderInfo::Default, s0(), app(bvar(0), a0.clone()));
            assert!(Rc::ptr_eq(&instantiate(&closed, &[x]), &closed));
        }
    }

    /// The same shared subterm under two binder depths must be substituted
    /// per depth: the memo key carries the depth, and a reused allocation
    /// must not carry entries from one call into the next.
    #[test]
    fn instantiate_memo_does_not_leak_between_calls() {
        let shared = app(bvar(0), bvar(1));
        let body = app(shared.clone(), lam(BinderInfo::Default, s0(), shared.clone()));
        let c1 = const_(21, vec![]);
        let c2 = const_(22, vec![]);
        let r1 = instantiate(&body, std::slice::from_ref(&c1));
        let r2 = instantiate(&body, std::slice::from_ref(&c2));
        assert!(Rc::ptr_eq(&r1, &instantiate_ref(&body, std::slice::from_ref(&c1), 0)));
        assert!(Rc::ptr_eq(&r2, &instantiate_ref(&body, std::slice::from_ref(&c2), 0)));
        assert!(!Rc::ptr_eq(&r1, &r2), "the second call saw the first call's entries");
    }

    #[test]
    fn short_circuit_never_changes_substitution() {
        let mut seed = 0x5EED_1234_u64;
        for _ in 0..400 {
            let e = gen(&mut seed, 5);
            let a0 = gen(&mut seed, 3);
            let a1 = gen(&mut seed, 3);
            for args in [vec![a0.clone()], vec![a0.clone(), a1.clone()]] {
                assert!(
                    Rc::ptr_eq(&instantiate(&e, &args), &instantiate_ref(&e, &args, 0)),
                    "instantiate diverged from the reference"
                );
            }
            for cutoff in 0..4u32 {
                assert!(
                    Rc::ptr_eq(&shift(&e, 2, cutoff), &shift_ref(&e, 2, cutoff)),
                    "shift diverged from the reference at cutoff {cutoff}"
                );
            }
        }
    }
}

#[cfg(test)]
#[path = "expr/level_subst_tests.rs"]
mod level_subst_tests;
