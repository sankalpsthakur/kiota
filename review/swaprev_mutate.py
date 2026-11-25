#!/usr/bin/env python3
"""Apply one named mutant of fix/mathlib-swap-v2 bcb623d to src/ (run from repo root).
Each replacement must match exactly once (the 'occurrence' index picks one of several)."""
import sys
M = {
 # memo freeze, globally and per guard
 "frz_all":   [("src/tc.rs", "pub(crate) fn memo_frozen() -> bool {\n    ABBREV_EXHAUSTED", "pub(crate) fn memo_frozen() -> bool {\n    false && ABBREV_EXHAUSTED", 0)],
 "frz_xinfer_hit": [("src/tc.rs", "                    if !memo_frozen() {\n                        cache_ref.borrow_mut().insert(key, (t.clone(), checked));", "                    if true {\n                        cache_ref.borrow_mut().insert(key, (t.clone(), checked));", 0)],
 "frz_infer": [("src/tc.rs", "        let t = self.infer_type_uncached(ctx, e)?;\n        if memo_frozen() {", "        let t = self.infer_type_uncached(ctx, e)?;\n        if false {", 0)],
 "frz_spine": [("src/tc.rs", "            if memo_frozen() {\n                continue;\n            }", "            if false {\n                continue;\n            }", 0)],
 "frz_proofarg": [("src/tc.rs", "        if !memo_frozen() {\n            self.proof_arg_cache", "        if true {\n            self.proof_arg_cache", 0)],
 "frz_xwhnf": [("src/tc.rs", "if xcache && !self.xcache_tainted.get() && !memo_frozen() {", "if xcache && !self.xcache_tainted.get() {", 0)],
 "frz_defeq": [("src/tc.rs", "    fn defeq_cache_insert(&self, force_eager: bool, key: (u64, usize, usize), v: bool) {\n        if memo_frozen() {", "    fn defeq_cache_insert(&self, force_eager: bool, key: (u64, usize, usize), v: bool) {\n        if false {", 0)],
 "frz_whnf": [("src/tc.rs", "    fn whnf_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if memo_frozen() {", "    fn whnf_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if false {", 0)],
 "frz_whnfcore": [("src/tc.rs", "    fn whnf_core_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if memo_frozen() {", "    fn whnf_core_cache_insert(&self, force_eager: bool, key: (u64, usize), v: Expr) {\n        if false {", 0)],
 "frz_iotalit": [("src/tc.rs", "if iota_memo_on && rest.is_empty() && !memo_frozen() {", "if iota_memo_on && rest.is_empty() {", 0)],
 "frz_nativestr": [("src/tc.rs", "                if !memo_frozen() {\n                    self.native_string_ok.set(Some(ok));", "                if true {\n                    self.native_string_ok.set(Some(ok));", 0)],
 "frz_iotaval": [("src/tc.rs", "        v: Rc<nbe::Value>,\n    ) {\n        if memo_frozen() {\n            return;\n        }", "        v: Rc<nbe::Value>,\n    ) {\n        if false {\n            return;\n        }", 0)],
 "frz_thunk": [("src/nbe.rs", "        if !crate::tc::memo_frozen() {\n            *self.0.borrow_mut()", "        if true {\n            *self.0.borrow_mut()", 0)],
 # frame logic
 "frm_no_entry_decline": [("src/tc.rs", "            if ABBREV_EXHAUSTED.with(Cell::get) {\n                DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));\n                return decline(\"abbrev argument comparison over budget\");\n            }", "", 0)],
 "frm_no_budget": [("src/tc.rs", "            if n > abbrev_args_budget() {\n                ABBREV_EXHAUSTED.with(|x| x.set(true));\n            }", "", 0)],
 "frm_keep_result": [("src/tc.rs", "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return Ok(false);", "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return r;", 0)],
 "frm_keep_true": [("src/tc.rs", "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return Ok(false);", "                return decline(\"abbrev argument comparisons over budget in this declaration\");\n            }\n            return Ok(matches!(r, Ok(true)));", 0)],
 "frm_core_aborted": [("src/tc.rs", "            ABBREV_EXHAUSTIONS.with(|n| n.set(n.get() + 1));\n            CORE_ABORTED.with(|c| c.set(abort_before));", "            ABBREV_EXHAUSTIONS.with(|n| n.set(n.get() + 1));", 0)],
 "frm_flag_sticky": [("src/tc.rs", "        if ABBREV_EXHAUSTED.with(|x| x.replace(false)) {", "        if ABBREV_EXHAUSTED.with(|x| x.get()) {", 0)],
 "frm_any_def": [("src/tc.rs", "Some(ConstantInfo::Def { hints: ReducibilityHints::Abbrev, .. }))\n        {\n            self.abbrev_args_frame(compare)?", "Some(ConstantInfo::Def { .. }))\n        {\n            self.abbrev_args_frame(compare)?", 0)],
 "frm_nested": [("src/tc.rs", "        let r = if !ABBREV_FRAME.with(Cell::get)\n            && matches!", "        let r = if true\n            && matches!", 0)],
 "frm_no_frame": [("src/tc.rs", "        let r = if !ABBREV_FRAME.with(Cell::get)\n            && matches!", "        let r = if false\n            && matches!", 0)],
 "frm_depth_exh": [("src/tc.rs", "            if ABBREV_EXHAUSTED.with(Cell::get) {\n                DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));", "            if ABBREV_EXHAUSTED.with(Cell::get) {", 0)],
 "frm_work_reset": [("src/tc.rs", "        ABBREV_FRAME.with(|f| f.set(true));\n        ABBREV_WORK.with(|w| w.set(0));", "        ABBREV_FRAME.with(|f| f.set(true));", 0)],
 # declaration cap
 "decl_no_entry_decline": [("src/tc.rs", "        if DECL_ABANDONED.with(Cell::get) {\n            DEFEQ_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));\n            return decline(\"abbrev argument comparisons over budget in this declaration\");\n        }", "", 0)],
 "decl_no_convert": [("src/tc.rs", "        let r = if DECL_ABANDONED.with(|a| a.replace(false)) {", "        let r = if { DECL_ABANDONED.with(|a| a.replace(false)); false } {", 0)],
 "decl_never_abandon": [("src/tc.rs", "            if n.is_some_and(|n| n >= MAX_DECL_EXHAUSTIONS) {", "            if false && n.is_some_and(|n| n >= MAX_DECL_EXHAUSTIONS) {", 0)],
 "decl_not_frozen": [("src/tc.rs", "    ABBREV_EXHAUSTED.with(Cell::get) || DECL_ABANDONED.with(Cell::get)\n}", "    ABBREV_EXHAUSTED.with(Cell::get)\n}", 0)],
 "decl_cap_off_by_one": [("src/tc.rs", "            if n.is_some_and(|n| n >= MAX_DECL_EXHAUSTIONS) {", "            if n.is_some_and(|n| n > MAX_DECL_EXHAUSTIONS) {", 0)],
 "decl_no_reset_start": [("src/tc.rs", "        DECL_ABANDONED.with(|a| a.set(false));\n        let outer", "        let outer", 0)],
 # decline propagation
 "prop_nested_swallow": [("src/tc.rs", "                        if !self.is_def_eq(ctx, a, b)? {\n                            matches = false;", "                        if !self.is_def_eq(ctx, a, b).unwrap_or(false) {\n                            matches = false;", 0)],
 "prop_mkrec_swallow": [("src/tc.rs", "            let w = self.whnf(&tctx, &cur)?;", "            let w = self.whnf(&tctx, &cur).unwrap_or_else(|_| cur.clone());", 0)],
}
if __name__ == "__main__":
    name = sys.argv[1]
    if name == "list":
        print(" ".join(M)); sys.exit(0)
    if name == "none":
        sys.exit(0)
    for path, old, new, _ in M[name]:
        s = open(path).read()
        c = s.count(old)
        if c != 1:
            sys.exit(f"{name}: {path}: pattern matched {c} times")
        open(path, "w").write(s.replace(old, new))
    print(f"applied {name}")
