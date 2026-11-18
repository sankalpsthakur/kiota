//! Opt-in counters for the hot paths. Enabled with `KIOTA_STATS=1`; the
//! counters are plain thread-local `Cell`s, so the disabled path is a
//! predictable branch and costs nothing measurable.

use std::cell::Cell;

thread_local! {
    static INFER_CALLS: Cell<u64> = const { Cell::new(0) };
    static WHNF_CALLS: Cell<u64> = const { Cell::new(0) };
    static DEFEQ_CALLS: Cell<u64> = const { Cell::new(0) };
    static INST_NODES: Cell<u64> = const { Cell::new(0) };
    static SHIFT_NODES: Cell<u64> = const { Cell::new(0) };
    static CTX_CLONES: Cell<u64> = const { Cell::new(0) };
    static INFER_HITS: Cell<u64> = const { Cell::new(0) };
    static WHNF_HITS: Cell<u64> = const { Cell::new(0) };
    static DEFEQ_HITS: Cell<u64> = const { Cell::new(0) };
    static CLOSED_MISS: [Cell<u64>; 3] = const { [Cell::new(0), Cell::new(0), Cell::new(0)] };
    static CLOSED_XHIT: [Cell<u64>; 3] = const { [Cell::new(0), Cell::new(0), Cell::new(0)] };
    static OPEN_MISS: [Cell<u64>; 3] = const { [Cell::new(0), Cell::new(0), Cell::new(0)] };
    static XSEEN: std::cell::RefCell<rustc_hash::FxHashSet<(u8, usize, usize)>> = std::cell::RefCell::new(Default::default());
}

pub fn enabled() -> bool {
    thread_local! {
        static ON: bool = std::env::var_os("KIOTA_STATS").is_some();
    }
    ON.with(|b| *b)
}

macro_rules! bump {
    ($name:ident, $cell:ident) => {
        #[inline(always)]
        pub fn $name() {
            if enabled() {
                $cell.with(|c| c.set(c.get() + 1));
            }
        }
    };
}

bump!(infer_call, INFER_CALLS);
bump!(whnf_call, WHNF_CALLS);
bump!(defeq_call, DEFEQ_CALLS);
bump!(inst_node, INST_NODES);
bump!(shift_node, SHIFT_NODES);
bump!(ctx_clone, CTX_CLONES);
bump!(infer_hit, INFER_HITS);
bump!(whnf_hit, WHNF_HITS);
bump!(defeq_hit, DEFEQ_HITS);

/// A per-declaration cache miss. Closed keys (context key 0) are looked up
/// in a set that outlives the declaration: a repeat there is work a cache
/// kept across declarations would have saved. kind: 0 infer, 1 whnf, 2 defeq.
pub fn miss(kind: u8, ctx_key: u64, a: usize, b: usize) {
    if !enabled() {
        return;
    }
    if ctx_key != 0 {
        OPEN_MISS.with(|c| c[kind as usize].set(c[kind as usize].get() + 1));
        return;
    }
    let fresh = XSEEN.with(|s| s.borrow_mut().insert((kind, a, b)));
    if fresh {
        CLOSED_MISS.with(|c| c[kind as usize].set(c[kind as usize].get() + 1));
    } else {
        CLOSED_XHIT.with(|c| c[kind as usize].set(c[kind as usize].get() + 1));
    }
}

/// Add a whole substitution's worth of nodes to `inst_nodes` at once.
#[inline]
pub fn inst_nodes_add(n: u64) {
    if enabled() {
        INST_NODES.with(|c| c.set(c.get() + n));
    }
}

pub fn inst_nodes() -> u64 {
    INST_NODES.with(|c| c.get())
}

pub fn whnf_calls() -> u64 {
    WHNF_CALLS.with(|c| c.get())
}

pub fn defeq_calls() -> u64 {
    DEFEQ_CALLS.with(|c| c.get())
}

pub fn infer_calls() -> u64 {
    INFER_CALLS.with(|c| c.get())
}

pub fn report() {
    if !enabled() {
        return;
    }
    let g = |c: &'static std::thread::LocalKey<Cell<u64>>| c.with(|x| x.get());
    let arr = |c: &'static std::thread::LocalKey<[Cell<u64>; 3]>| c.with(|x| [x[0].get(), x[1].get(), x[2].get()]);
    eprintln!(
        "STATS2 whnf_hit={} defeq_hit={} closed_first_miss(infer,whnf,defeq)={:?} closed_cross_decl_repeat={:?} open_miss={:?}",
        g(&WHNF_HITS), g(&DEFEQ_HITS), arr(&CLOSED_MISS), arr(&CLOSED_XHIT), arr(&OPEN_MISS),
    );
    eprintln!("STATS3 xcache_hits={}", crate::tc::xcache_hits());
    report_sites();
    eprintln!(
        "STATS infer={} infer_hit={} whnf={} defeq={} inst_nodes={} shift_nodes={} ctx_clones={} intern_calls={} live_nodes={}",
        g(&INFER_CALLS),
        g(&INFER_HITS),
        g(&WHNF_CALLS),
        g(&DEFEQ_CALLS),
        g(&INST_NODES),
        g(&SHIFT_NODES),
        g(&CTX_CLONES),
        crate::expr::intern_calls(),
        crate::expr::intern_node_count(),
    );
}

// ---------------------------------------------------------------------
// Call-site attribution (`KIOTA_STATS=1`, STATS4..STATS7 lines).
//
// Every interned node is charged to the checker call site that asked for
// it (`site`) and to the primitive that built it (`op`). A site tag is set
// only around the substitution call itself, never across the recursive
// inference or reduction of the same arm, so a row is that site's own work.

pub mod site {
    pub const PARSE: u8 = 0;
    pub const CHECK_OTHER: u8 = 1;
    pub const INFER_APP: u8 = 2;
    pub const INFER_LET: u8 = 3;
    pub const INFER_CONST: u8 = 4;
    pub const INFER_PROJ: u8 = 5;
    pub const DEFEQ_ARGS: u8 = 6;
    pub const LAZY_HEAD: u8 = 7;
    pub const WHNF_BETA: u8 = 8;
    pub const WHNF_ZETA: u8 = 9;
    pub const DEFEQ_LET: u8 = 10;
    pub const UNFOLD: u8 = 11;
    pub const LOCAL_TY: u8 = 12;
    pub const ETA: u8 = 13;
    pub const IOTA: u8 = 14;
    pub const WHNF_MAJOR: u8 = 15;
    pub const APPS: u8 = 16;
    pub const INFER_LAM_PI: u8 = 17;
    pub const N: usize = 18;
    pub const NAMES: [&str; N] = [
        "parse", "check_other", "infer_app", "infer_let", "infer_const", "infer_proj",
        "defeq_args", "lazy_head", "whnf_beta", "whnf_zeta", "defeq_let", "unfold",
        "local_ty", "eta", "iota", "whnf_major", "apps", "infer_lam_pi",
    ];
}

pub mod op {
    pub const DIRECT: u8 = 0;
    pub const INST: u8 = 1;
    pub const SHIFT: u8 = 2;
    pub const LEVEL: u8 = 3;
    pub const N: usize = 4;
    pub const NAMES: [&str; N] = ["direct", "inst", "shift", "level"];
}

const KINDS: [&str; 9] = ["bvar", "sort", "const", "app", "lam", "pi", "let", "proj", "lit"];

thread_local! {
    static SITE: Cell<u8> = const { Cell::new(0) };
    static OP: Cell<u8> = const { Cell::new(0) };
    static INTERN_BY: [Cell<u64>; site::N * op::N] = const { [const { Cell::new(0) }; site::N * op::N] };
    static ALLOC_BY: [Cell<u64>; site::N * op::N] = const { [const { Cell::new(0) }; site::N * op::N] };
    /// Per site: instantiate calls, `instantiate1` memo hits, calls whose
    /// argument the body never mentions, substitution nodes those built.
    static SUBST_CALLS: [Cell<u64>; site::N] = const { [const { Cell::new(0) }; site::N] };
    static SUBST_MEMO_HITS: [Cell<u64>; site::N] = const { [const { Cell::new(0) }; site::N] };
    static SUBST_UNUSED: [Cell<u64>; site::N] = const { [const { Cell::new(0) }; site::N] };
    static SUBST_UNUSED_NODES: [Cell<u64>; site::N] = const { [const { Cell::new(0) }; site::N] };
    static SUBST_NODES: [Cell<u64>; site::N] = const { [const { Cell::new(0) }; site::N] };
    /// kind(9) x open(2) x derived(2) x infer_only(2)
    static INFER_MISS: [Cell<u64>; 72] = const { [const { Cell::new(0) }; 72] };
    static INFER_UPGRADE: Cell<u64> = const { Cell::new(0) };
    static INFER_FALLBACK: Cell<u64> = const { Cell::new(0) };
    static INFER_REKEY: Cell<u64> = const { Cell::new(0) };
    static INFER_REKEY_CHECK: Cell<u64> = const { Cell::new(0) };
    /// open(2) x derived(2)
    static WHNF_MISS: [Cell<u64>; 4] = const { [const { Cell::new(0) }; 4] };
    static WHNF_FALLBACK: Cell<u64> = const { Cell::new(0) };
    static WHNF_TRIVIAL: Cell<u64> = const { Cell::new(0) };
    static CORE_CALLS: Cell<u64> = const { Cell::new(0) };
    static CORE_HITS: Cell<u64> = const { Cell::new(0) };
    static WATERMARK: Cell<usize> = const { Cell::new(usize::MAX) };
    static SEEN_KEY: std::cell::RefCell<rustc_hash::FxHashMap<usize, u64>> = std::cell::RefCell::new(Default::default());
}

/// Restores the previous site tag when dropped.
pub struct SiteGuard(u8);

impl Drop for SiteGuard {
    #[inline(always)]
    fn drop(&mut self) {
        if self.0 != u8::MAX {
            SITE.with(|c| c.set(self.0));
        }
    }
}

#[inline(always)]
pub fn at(s: u8) -> SiteGuard {
    if !enabled() {
        return SiteGuard(u8::MAX);
    }
    SiteGuard(SITE.with(|c| c.replace(s)))
}

/// Restores the previous primitive tag when dropped.
pub struct OpGuard(u8);

impl Drop for OpGuard {
    #[inline(always)]
    fn drop(&mut self) {
        if self.0 != u8::MAX {
            OP.with(|c| c.set(self.0));
        }
    }
}

#[inline(always)]
pub fn op(o: u8) -> OpGuard {
    if !enabled() {
        return OpGuard(u8::MAX);
    }
    OpGuard(OP.with(|c| c.replace(o)))
}

#[inline(always)]
fn cell_index() -> usize {
    SITE.with(|c| c.get()) as usize * op::N + OP.with(|c| c.get()) as usize
}

#[inline(always)]
pub fn intern_tick() {
    if enabled() {
        let i = cell_index();
        INTERN_BY.with(|t| t[i].set(t[i].get() + 1));
    }
}

#[inline(always)]
pub fn alloc_tick() {
    if enabled() {
        let i = cell_index();
        ALLOC_BY.with(|t| t[i].set(t[i].get() + 1));
    }
}

/// One `instantiate`/`instantiate1` call at the current site. `memo_hit`:
/// answered by the `instantiate1` memo. `unused`: the body does not mention
/// the bound variable, so the call only renumbers. `nodes`: substitution
/// nodes it visited.
pub fn subst_call(memo_hit: bool, unused: bool, nodes: u64) {
    if !enabled() {
        return;
    }
    let s = SITE.with(|c| c.get()) as usize;
    SUBST_CALLS.with(|t| t[s].set(t[s].get() + 1));
    if memo_hit {
        SUBST_MEMO_HITS.with(|t| t[s].set(t[s].get() + 1));
    }
    if unused {
        SUBST_UNUSED.with(|t| t[s].set(t[s].get() + 1));
        SUBST_UNUSED_NODES.with(|t| t[s].set(t[s].get() + nodes));
    }
    SUBST_NODES.with(|t| t[s].set(t[s].get() + nodes));
}

/// Start of a declaration's check: nodes with an identity at or past
/// `watermark` were built while checking it rather than read from the export.
pub fn decl_start(watermark: usize) {
    if !enabled() {
        return;
    }
    WATERMARK.with(|c| c.set(watermark));
    SEEN_KEY.with(|m| m.borrow_mut().clear());
    SPINE_SUBST_SEEN.with(|m| m.borrow_mut().clear());
    SITE.with(|c| c.set(site::CHECK_OTHER));
}

pub fn decl_end() {
    if enabled() {
        SITE.with(|c| c.set(site::PARSE));
        WATERMARK.with(|c| c.set(usize::MAX));
    }
}

#[allow(clippy::too_many_arguments)]
pub fn infer_miss(
    kind: u8,
    identity: usize,
    ctx_key: u64,
    full_ctx_id: u64,
    infer_only: bool,
    upgrade: bool,
) {
    if !enabled() {
        return;
    }
    let open = ctx_key != 0;
    let derived = identity >= WATERMARK.with(|c| c.get());
    let i = ((kind as usize * 2 + open as usize) * 2 + derived as usize) * 2 + infer_only as usize;
    INFER_MISS.with(|t| t[i].set(t[i].get() + 1));
    if upgrade {
        INFER_UPGRADE.with(|c| c.set(c.get() + 1));
    }
    if open {
        if ctx_key == full_ctx_id {
            INFER_FALLBACK.with(|c| c.set(c.get() + 1));
        }
        let rekey = SEEN_KEY.with(|m| {
            let mut m = m.borrow_mut();
            match m.get(&identity) {
                Some(k) => *k != ctx_key,
                None => {
                    m.insert(identity, ctx_key);
                    false
                }
            }
        });
        if rekey {
            INFER_REKEY.with(|c| c.set(c.get() + 1));
            if !infer_only {
                INFER_REKEY_CHECK.with(|c| c.set(c.get() + 1));
            }
        }
    }
}

pub fn whnf_miss(identity: usize, ctx_key: u64, full_ctx_id: u64, trivial: bool) {
    if !enabled() {
        return;
    }
    let open = ctx_key != 0;
    let derived = identity >= WATERMARK.with(|c| c.get());
    let i = open as usize * 2 + derived as usize;
    WHNF_MISS.with(|t| t[i].set(t[i].get() + 1));
    if open && ctx_key == full_ctx_id {
        WHNF_FALLBACK.with(|c| c.set(c.get() + 1));
    }
    if trivial {
        WHNF_TRIVIAL.with(|c| c.set(c.get() + 1));
    }
}

thread_local! {
    static SPINE_SUBST_SEEN: std::cell::RefCell<rustc_hash::FxHashSet<(usize, Vec<usize>)>> = std::cell::RefCell::new(Default::default());
    static SPINE_SUBST: [Cell<u64>; 4] = const { [const { Cell::new(0) }; 4] };
}

/// One substitution of pending spine arguments into `term`. A repeat is the
/// same term with the same arguments again in this declaration: a memo on
/// that pair would have answered it. `nodes`: substitution nodes it built.
pub fn spine_subst(term: usize, args: Vec<usize>, nodes: u64) {
    if !enabled() || nodes == 0 {
        return;
    }
    let fresh = SPINE_SUBST_SEEN.with(|m| m.borrow_mut().insert((term, args)));
    let base = if fresh { 0 } else { 2 };
    SPINE_SUBST.with(|t| {
        t[base].set(t[base].get() + 1);
        t[base + 1].set(t[base + 1].get() + nodes);
    });
}

bump!(core_call, CORE_CALLS);
bump!(core_hit, CORE_HITS);

fn report_sites() {
    let g = |c: &'static std::thread::LocalKey<Cell<u64>>| c.with(|x| x.get());
    for s in 0..site::N {
        let row: Vec<u64> = (0..op::N).map(|o| INTERN_BY.with(|t| t[s * op::N + o].get())).collect();
        let new: Vec<u64> = (0..op::N).map(|o| ALLOC_BY.with(|t| t[s * op::N + o].get())).collect();
        let calls = SUBST_CALLS.with(|t| t[s].get());
        if row.iter().sum::<u64>() == 0 && calls == 0 {
            continue;
        }
        eprintln!(
            "STATS4 site={} interns(direct,inst,shift,level)={:?} new_nodes={:?} subst_calls={} memo_hits={} subst_nodes={} unused_arg_calls={} unused_arg_nodes={}",
            site::NAMES[s],
            row,
            new,
            calls,
            SUBST_MEMO_HITS.with(|t| t[s].get()),
            SUBST_NODES.with(|t| t[s].get()),
            SUBST_UNUSED.with(|t| t[s].get()),
            SUBST_UNUSED_NODES.with(|t| t[s].get()),
        );
    }
    // kind: [closed/export, closed/derived, open/export, open/derived] x [check, infer_only]
    for k in 0..9 {
        let cells: Vec<u64> = (0..8).map(|j| INFER_MISS.with(|t| t[k * 8 + j].get())).collect();
        if cells.iter().sum::<u64>() == 0 {
            continue;
        }
        eprintln!(
            "STATS5 infer_miss kind={} closed_export(check,only)={:?} closed_derived={:?} open_export={:?} open_derived={:?}",
            KINDS[k],
            &cells[0..2],
            &cells[2..4],
            &cells[4..6],
            &cells[6..8],
        );
    }
    eprintln!(
        "STATS6 infer_upgrade_unchecked_to_checked={} infer_open_key_is_full_ctx={} infer_open_rekey={} infer_open_rekey_check_mode={}",
        g(&INFER_UPGRADE),
        g(&INFER_FALLBACK),
        g(&INFER_REKEY),
        g(&INFER_REKEY_CHECK),
    );
    let sp: Vec<u64> = (0..4).map(|j| SPINE_SUBST.with(|t| t[j].get())).collect();
    eprintln!(
        "STATS8 spine_subst first(calls,nodes)={:?} repeat_same_term_and_args(calls,nodes)={:?}",
        &sp[0..2],
        &sp[2..4],
    );
    let [same, rebuilt] = crate::tc::spine_verified();
    if same + rebuilt > 0 {
        eprintln!("STATS9 spine_verify same_node={same} same_term_other_node={rebuilt}");
    }
    let w: Vec<u64> = (0..4).map(|j| WHNF_MISS.with(|t| t[j].get())).collect();
    eprintln!(
        "STATS7 whnf_miss(closed_export,closed_derived,open_export,open_derived)={:?} whnf_open_key_is_full_ctx={} whnf_miss_already_pi_sort_lam={} whnf_core_calls={} whnf_core_hits={}",
        w,
        g(&WHNF_FALLBACK),
        g(&WHNF_TRIVIAL),
        g(&CORE_CALLS),
        g(&CORE_HITS),
    );
}

/// `KIOTA_TRACE_NEQ=1` logs every definitional-equality comparison that comes
/// back false. Reading the *smallest* failing pair is how the projection and
/// shared-head congruence gaps were found: the outer failures are just the
/// enclosing terms, and the innermost one names the actual defect. Note that
/// the printed forms are budget-truncated, so diff them with care — a "first
/// divergence" computed on truncated output can be an artifact.
pub fn trace_neq() -> bool {
    thread_local! {
        static ON: bool = std::env::var_os("KIOTA_TRACE_NEQ").is_some();
    }
    ON.with(|b| *b)
}

thread_local! {
    static VERBOSE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Enable verbose defeq tracing while checking the named declaration.
/// `KIOTA_TRACE_TARGET` selects which declaration (default: fixF_eq).
pub fn set_verbose_target(name: &str) {
    let on = std::env::var("KIOTA_TRACE_TARGET")
        .ok()
        .filter(|t| !t.is_empty())
        .is_some_and(|t| name.contains(&t));
    VERBOSE.with(|c| c.set(on));
}

pub fn verbose() -> bool {
    VERBOSE.with(|c| c.get())
}

thread_local! {
    static THEOREM_DELTA_SCOPE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Scope theorem-unfolding to the decl currently being checked, so a single
/// theorem can be unfolded without letting the delta path tear through every
/// large proof body in the environment. With `KIOTA_THEOREM_DELTA_TARGET` set,
/// theorem delta applies only while checking a decl whose name contains the
/// substring; unset means the scope is global.
pub fn set_theorem_delta_scope(name: &str) {
    let on = match std::env::var("KIOTA_THEOREM_DELTA_TARGET") {
        Ok(t) if !t.is_empty() => name.contains(&t),
        _ => true,
    };
    THEOREM_DELTA_SCOPE.with(|c| c.set(on));
}

pub fn theorem_delta_in_scope() -> bool {
    THEOREM_DELTA_SCOPE.with(|c| c.get())
}

/// Decision histogram: theorem delta, PI infer-only and Nat-literal shortcuts.
/// On when `KIOTA_SHORTCUT_JSON` or `KIOTA_STATS` is set.
pub fn shortcut_enabled() -> bool {
    thread_local! {
        static ON: bool = std::env::var_os("KIOTA_SHORTCUT_JSON").is_some()
            || std::env::var_os("KIOTA_STATS").is_some();
    }
    ON.with(|b| *b)
}

macro_rules! sc_bump {
    ($name:ident, $cell:ident) => {
        #[inline(always)]
        pub fn $name() {
            if shortcut_enabled() {
                $cell.with(|c| c.set(c.get() + 1));
            }
        }
    };
}

thread_local! {
    static C_THM_DELTA_OFF: Cell<u64> = const { Cell::new(0) };
    static K_PI_INFER_ONLY: Cell<u64> = const { Cell::new(0) };
    static N_NAT: Cell<u64> = const { Cell::new(0) };
}

sc_bump!(c_thm_delta_off, C_THM_DELTA_OFF);
sc_bump!(k_pi_infer_only, K_PI_INFER_ONLY);
sc_bump!(n_nat, N_NAT);

pub fn report_shortcuts() {
    if !shortcut_enabled() {
        return;
    }
    let g = |c: &'static std::thread::LocalKey<Cell<u64>>| c.with(|x| x.get());
    eprintln!(
        "{{\"kiota_shortcuts\":{{\"C_thm_delta_off\":{},\"K_pi_infer_only\":{},\"N_nat\":{}}}}}",
        g(&C_THM_DELTA_OFF),
        g(&K_PI_INFER_ONLY),
        g(&N_NAT),
    );
}

#[cfg(test)]
mod tests {
    #[test]
    fn unset_theorem_delta_is_global() {
        // Unset `KIOTA_THEOREM_DELTA_TARGET` must not key on `fixF_eq`.
        std::env::remove_var("KIOTA_THEOREM_DELTA_TARGET");
        super::set_theorem_delta_scope("Nat.add_comm");
        assert!(
            super::theorem_delta_in_scope(),
            "unset theorem-delta scope is global"
        );
        super::set_theorem_delta_scope("WellFounded.fixF_eq");
        assert!(super::theorem_delta_in_scope());
    }
}
