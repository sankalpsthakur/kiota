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

pub fn report() {
    if !enabled() {
        return;
    }
    let g = |c: &'static std::thread::LocalKey<Cell<u64>>| c.with(|x| x.get());
    eprintln!(
        "STATS infer={} infer_hit={} whnf={} defeq={} inst_nodes={} shift_nodes={} ctx_clones={}",
        g(&INFER_CALLS),
        g(&INFER_HITS),
        g(&WHNF_CALLS),
        g(&DEFEQ_CALLS),
        g(&INST_NODES),
        g(&SHIFT_NODES),
        g(&CTX_CLONES),
    );
}
