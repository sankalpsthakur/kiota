"""Mutants of the abbrev argument frame (fix/mathlib-swap-v2).

python3 scripts/mut/mutate.py list       -> mutant names, one per line
python3 scripts/mut/mutate.py <name>     -> apply that mutant in place
"control" applies nothing. Each anchor must occur exactly once.
"""
import sys

TC = "src/tc.rs"
NBE = "src/nbe.rs"

M = {
    # The frame itself.
    "M1_no_frame_entry": (TC,
        "let r = if !ABBREV_FRAME.with(Cell::get)\n            && matches!",
        "let r = if false && !ABBREV_FRAME.with(Cell::get)\n            && matches!"),
    "M2_no_budget_check": (TC,
        "if n > abbrev_args_budget() {",
        "if false && n > abbrev_args_budget() {"),
    "M3_no_decline_when_exhausted": (TC,
        "            if ABBREV_EXHAUSTED.with(Cell::get) {\n                DEFEQ_DEPTH",
        "            if false && ABBREV_EXHAUSTED.with(Cell::get) {\n                DEFEQ_DEPTH"),
    "M4_keep_result_when_exhausted": (TC,
        "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return Ok(false);",
        "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return r;"),
    "M5_no_core_aborted_restore": (TC,
        "            CORE_ABORTED.with(|c| c.set(abort_before));\n            if let Some(t0) = t0 {\n                let us",
        "            if let Some(t0) = t0 {\n                let us"),
    "M13_no_depth_restore_on_budget_decline": (TC,
        "                DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));\n                return decline(\"abbrev argument comparison over budget\");",
        "                return decline(\"abbrev argument comparison over budget\");"),
    "M14_exhausted_flag_not_cleared": (TC,
        "if ABBREV_EXHAUSTED.with(|x| x.replace(false)) {",
        "if ABBREV_EXHAUSTED.with(Cell::get) {"),
    "M15_nested_frames": (TC,
        "let r = if !ABBREV_FRAME.with(Cell::get)\n            && matches!",
        "let r = if true\n            && matches!"),
    "M16_no_frame_reset": (TC,
        "        let r = compare();\n        ABBREV_FRAME.with(|f| f.set(false));\n",
        "        let r = compare();\n"),
    "M17_any_def": (TC,
        "Some(ConstantInfo::Def { hints: ReducibilityHints::Abbrev, .. }))\n        {\n            self.abbrev_args_frame",
        "Some(ConstantInfo::Def { .. }))\n        {\n            self.abbrev_args_frame"),
    # The memo freeze.
    "M6_infer_cache_not_frozen": (TC,
        "        let t = self.infer_type_uncached(ctx, e)?;\n        if memo_frozen() {",
        "        let t = self.infer_type_uncached(ctx, e)?;\n        if false && memo_frozen() {"),
    "M6b_xinfer_copy_not_frozen": (TC,
        "XCACHE_HITS.with(|c| c.set(c.get() + 1));\n                    if !memo_frozen() {",
        "XCACHE_HITS.with(|c| c.set(c.get() + 1));\n                    if true {"),
    "M7_spine_not_frozen": (TC,
        "            if memo_frozen() {\n                continue;\n            }\n",
        ""),
    "M8_defeq_cache_not_frozen": (TC,
        "    fn defeq_cache_insert(&self, force_eager: bool, key: (u64, usize, usize), v: bool) {\n        if memo_frozen() {",
        "    fn defeq_cache_insert(&self, force_eager: bool, key: (u64, usize, usize), v: bool) {\n        if false && memo_frozen() {"),
    "M9_whnf_cache_not_frozen": (TC,
        "    fn whnf_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if memo_frozen() {",
        "    fn whnf_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if false && memo_frozen() {"),
    "M9b_xwhnf_not_frozen": (TC,
        "if xcache && !self.xcache_tainted.get() && !memo_frozen() {\n            XWHNF",
        "if xcache && !self.xcache_tainted.get() {\n            XWHNF"),
    "M10_whnf_core_cache_not_frozen": (TC,
        "    fn whnf_core_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if memo_frozen() {",
        "    fn whnf_core_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if false && memo_frozen() {"),
    "M11_iota_lit_memo_not_frozen": (TC,
        "rest.is_empty() && !memo_frozen() {",
        "rest.is_empty() {"),
    "M12_iota_value_cache_not_frozen": (TC,
        "        args: &[Rc<nbe::Thunk>],\n        v: Rc<nbe::Value>,\n    ) {\n        if memo_frozen() {",
        "        args: &[Rc<nbe::Thunk>],\n        v: Rc<nbe::Value>,\n    ) {\n        if false && memo_frozen() {"),
    "M18_proof_arg_cache_not_frozen": (TC,
        "        if !memo_frozen() {\n            self.proof_arg_cache",
        "        if true {\n            self.proof_arg_cache"),
    "M19_native_string_not_frozen": (TC,
        "                if !memo_frozen() {\n                    self.native_string_ok",
        "                if true {\n                    self.native_string_ok"),
    "M20_thunk_not_frozen": (NBE,
        "if !crate::tc::memo_frozen() {",
        "if true {"),
    # Declines that used to be swallowed.
    "M21_nested_rec_for_type_swallows": (TC,
        "                        if !self.is_def_eq(ctx, a, b)? {\n                            matches = false;",
        "                        if !self.is_def_eq(ctx, a, b).unwrap_or(false) {\n                            matches = false;"),
    "M22_mk_rec_call_swallows": (TC,
        "            let w = self.whnf(&tctx, &cur)?;",
        "            let w = self.whnf(&tctx, &cur).unwrap_or_else(|_| cur.clone());"),
    # The per-declaration cap.
    "M23_no_decl_cap": (TC,
        "if n.is_some_and(|n| n >= MAX_DECL_EXHAUSTIONS) {",
        "if false && n.is_some_and(|n| n >= MAX_DECL_EXHAUSTIONS) {"),
    "M24_abandoned_pass_compares_on": (TC,
        "        if DECL_ABANDONED.with(Cell::get) {\n            DEFEQ_DEPTH",
        "        if false && DECL_ABANDONED.with(Cell::get) {\n            DEFEQ_DEPTH"),
    "M25_abandoned_pass_verdict_kept": (TC,
        "        let r = if DECL_ABANDONED.with(|a| a.replace(false)) {",
        "        let r = if { DECL_ABANDONED.with(|a| a.set(false)); false } {"),
    "M26_abandoned_pass_memoizes": (TC,
        "ABBREV_EXHAUSTED.with(Cell::get) || DECL_ABANDONED.with(Cell::get)",
        "ABBREV_EXHAUSTED.with(Cell::get)"),
    "M27_abandoned_entry_depth_leak": (TC,
        "        if DECL_ABANDONED.with(Cell::get) {\n            DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));\n",
        "        if DECL_ABANDONED.with(Cell::get) {\n"),
}

if __name__ == "__main__":
    name = sys.argv[1]
    if name == "list":
        print("control")
        print("\n".join(M))
        sys.exit(0)
    if name == "control":
        sys.exit(0)
    path, a, b = M[name]
    src = open(path).read()
    n = src.count(a)
    assert n == 1, (name, n)
    open(path, "w").write(src.replace(a, b))
    print(f"applied {name} to {path}")
