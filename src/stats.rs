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

/// Decision histogram: fundamentals vs name-gates vs library interpreters.
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
    static N_INT: Cell<u64> = const { Cell::new(0) };
    static L_LINEAR: Cell<u64> = const { Cell::new(0) };
    static L_COMMRING: Cell<u64> = const { Cell::new(0) };
    static L_RAT: Cell<u64> = const { Cell::new(0) };
    static L_OMEGA: Cell<u64> = const { Cell::new(0) };
}

sc_bump!(c_thm_delta_off, C_THM_DELTA_OFF);
sc_bump!(k_pi_infer_only, K_PI_INFER_ONLY);
sc_bump!(n_nat, N_NAT);
sc_bump!(n_int, N_INT);
sc_bump!(l_linear, L_LINEAR);
sc_bump!(l_commring, L_COMMRING);
sc_bump!(l_rat, L_RAT);
sc_bump!(l_omega, L_OMEGA);

pub fn report_shortcuts() {
    if !shortcut_enabled() {
        return;
    }
    let g = |c: &'static std::thread::LocalKey<Cell<u64>>| c.with(|x| x.get());
    eprintln!(
        "{{\"kiota_shortcuts\":{{\"C_thm_delta_off\":{},\"K_pi_infer_only\":{},\"N_nat\":{},\"N_int\":{},\"L_linear\":{},\"L_commring\":{},\"L_rat\":{},\"L_omega\":{}}}}}",
        g(&C_THM_DELTA_OFF),
        g(&K_PI_INFER_ONLY),
        g(&N_NAT),
        g(&N_INT),
        g(&L_LINEAR),
        g(&L_COMMRING),
        g(&L_RAT),
        g(&L_OMEGA),
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
