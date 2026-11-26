#!/usr/bin/env python3
"""mutate.py ID [ROOT]: apply one mutant to fix/deep-evaluation-v3's src/.
Each edit is (file, exact old text, new text); the old text must occur exactly
once, or the script exits 3 (the mutant is then an error, not a kill).
R-numbers follow the round-2 review's list (44edff2); U/L/A are new sites."""
import os, sys
T = 'src/tc.rs'
L = 'CUT_SHORT.with(|c| c.set(cut));'
M = {
 'M00_none': [],
 'R01_open_terms_driven': [(T, 'if expr::loose_bvar_range(e) > 0 || env_set!("KIOTA_NO_NAT_DRIVER") {', 'if env_set!("KIOTA_NO_NAT_DRIVER") {')],
 'R02_nat_values_kept_across_decls': [(T, '        NAT_VALUES.with(|m| *m.borrow_mut() = FxHashMap::default());\n        match self.check_decl_once(name, kind) {', '        match self.check_decl_once(name, kind) {')],
 'R03_no_nat_values_lookup': [(T, 'if let Some(v) = NAT_VALUES.with(|m| m.borrow().get(&key)', 'if let Some(v) = NAT_VALUES.with(|m| m.borrow().get(&usize::MAX)')],
 'R04_no_nat_memo_lookup': [(T, 'if let Some(v) = NAT_MEMO.with(|m| m.borrow().get(&key)', 'if let Some(v) = NAT_MEMO.with(|m| m.borrow().get(&usize::MAX)')],
 'R05_no_early_decline_while_unwinding': [(T, '        if nat_unwinding() {\n            return decline("closed Nat argument suspended', '        if false {\n            return decline("closed Nat argument suspended')],
 'R06_never_suspend': [(T, 'let deep = w >= bw.saturating_add(NAT_STRIDE)', 'let deep = false && w >= bw.saturating_add(NAT_STRIDE)'), (T, '|| c >= bc.saturating_add(NAT_STRIDE)\n            || w.max(c) >= CONV_DEPTH - NAT_MARGIN;', '|| false;')],
 'R07_no_whnf_stride': [(T, 'let deep = w >= bw.saturating_add(NAT_STRIDE)', 'let deep = false')],
 'R08_no_core_stride': [(T, '|| c >= bc.saturating_add(NAT_STRIDE)', '|| false')],
 'R09_no_margin': [(T, '|| w.max(c) >= CONV_DEPTH - NAT_MARGIN;', '|| false;')],
 'U1_unwinding_not_frozen': [(T, 'ABBREV_EXHAUSTED.with(Cell::get) || DECL_ABANDONED.with(Cell::get) || nat_unwinding()', 'ABBREV_EXHAUSTED.with(Cell::get) || DECL_ABANDONED.with(Cell::get)')],
 'U2_unwinding_never_set': [(T, '            NAT_UNWINDING.with(|u| u.set(true));\n', '')],
 'R13_defeq_false_memo_always': [(T, 'if cacheable && (r || !CUT_SHORT.with(Cell::get)) {', 'if cacheable {')],
 'R14_xwhnf_ignores_cut': [(T, '&& !memo_frozen() && !CUT_SHORT.with(Cell::get) {', '&& !memo_frozen() {')],
 'R15_driver_keeps_ok_after_suspension': [(T, 'if let Some(x) = NAT_SUSPENDED.with(|s| s.borrow_mut().take()) {', 'if let Some(x) = NAT_SUSPENDED.with(|s| s.borrow_mut().take()).filter(|_| r.is_err()) {')],
 'R16_no_again_check': [(T, 'let again = pending.iter()', 'let again = false && pending.iter()')],
 'R17_no_pending_cap': [(T, '|| pending.len() >= NAT_PENDING_CAP.with(Cell::get)', '|| false')],
 'R18_no_suspension_cap': [(T, '|| suspensions > NAT_SUSPENSION_CAP.with(Cell::get)', '|| false')],
 'R19_remember_while_unwinding': [(T, 'if nat::as_lit(v).is_some() && !memo_frozen() {', 'if nat::as_lit(v).is_some() {')],
 'R20_driver_no_cut_restore': [(T, '                NAT_UNWINDING.with(|u| u.set(false));\n                ' + L, '                NAT_UNWINDING.with(|u| u.set(false));')],
 'R21_no_conclusive_decl': [(T, 'let r = Self::conclusive(|| self.check_decl_once_go(name, kind));', 'let r = self.check_decl_once_go(name, kind);')],
 'R22_no_conclusive_ind_structure': [(T, 'Self::conclusive(|| self.check_inductive_group_structure_go(first_name))', 'self.check_inductive_group_structure_go(first_name)')],
 'R23_no_conclusive_large_elim': [(T, 'Self::conclusive(|| self.check_inductive_group_large_elim(first_name))', 'self.check_inductive_group_large_elim(first_name)')],
 'R24_limit_hit_sets_no_cut': [(T, '    LIMIT_HITS.with(|c| c.set(c.get() + 1));\n    CUT_SHORT.with(|c| c.set(true));', '    LIMIT_HITS.with(|c| c.set(c.get() + 1));')],
 'R25_ensure_depth_uncounted': [(T, 'note_limit_hit("ensure depth");', '')],
 'R26_infer_depth_uncounted': [(T, 'note_limit_hit("infer depth");', '')],
 'R27_whnf_depth_uncounted': [(T, 'note_limit_hit("whnf depth");', '')],
 'R28_core_depth_uncounted': [(T, 'note_limit_hit("core depth");', '')],
 'R29_defeq_depth_uncounted': [(T, 'note_limit_hit("defeq depth");', '')],
 'R30_huge_run_uncounted': [(T, 'note_limit_hit("huge literal run");', '')],
 'R31_peel_budget_uncounted': [(T, 'note_limit_hit("peel budget");', '')],
 'R32_driver_budget_uncounted': [(T, 'note_limit_hit("nat driver budget");', '')],
 'L1_lazy_delta_cap_uncounted': [(T, 'note_limit_hit("lazy delta at core depth");', '')],
 'A1_abbrev_exhaustion_keeps_cut': [(T, '            CUT_SHORT.with(|c| c.set(cut_before));\n', '')],
 'R33_no_shape_clear': [(T, 'if CUT_SHORT.with(Cell::get) && self.whnf_by_shape(r) {', 'if false {')],
 'R34_true_keeps_cut': [(T, 'c.set(cut || (c.get() && !matches!(r, Ok(true))))', 'c.set(cut || c.get())')],
 'R35_defeq_drops_entry_cut': [(T, 'c.set(cut || (c.get() && !matches!(r, Ok(true))))', 'c.set(c.get() && !matches!(r, Ok(true)))')],
 'R36_whnf_drops_entry_cut': [(T, '        let r = self.whnf_miss(ctx, e, k, force_eager, xcache);\n        CUT_SHORT.with(|c| c.set(cut || c.get()));', '        let r = self.whnf_miss(ctx, e, k, force_eager, xcache);\n        let _ = cut;')],
 'R37_core_drops_entry_cut': [(T, '            self.whnf_core_cache_insert(force_eager, k, r.clone());\n        }\n        CUT_SHORT.with(|c| c.set(cut || c.get()));', '            self.whnf_core_cache_insert(force_eager, k, r.clone());\n        }\n        let _ = cut;')],
 'R38_no_cache_marks': [(T, 'mark_cut_short_key(force_eager as u8, key, CUT_SHORT.with(Cell::get));', 'mark_cut_short_key(force_eager as u8, key, false);'), (T, 'mark_cut_short_key(2 + force_eager as u8, key, CUT_SHORT.with(Cell::get));', 'mark_cut_short_key(2 + force_eager as u8, key, false);')],
 'R39_no_cache_mark_reads': [(T, 'if r.is_some() && cut_short_key(force_eager as u8, key) {', 'if false && cut_short_key(force_eager as u8, key) {'), (T, 'if r.is_some() && cut_short_key(2 + force_eager as u8, key) {', 'if false && cut_short_key(2 + force_eager as u8, key) {')],
 'R40_no_speculative_restore': [(T, '            let r = self.try_speculative_congruence(ctx, a, b);\n            ' + L + '\n            if r? {', '            let r = self.try_speculative_congruence(ctx, a, b);\n            if r? {'), (T, '            SPECULATING.with(|s| s.set(false));\n            ' + L, '            SPECULATING.with(|s| s.set(false));')],
 'R41_no_lazy_head_restore': [(T, '            let r = self.try_lazy_head_congruence(ctx, a, b);\n            ' + L, '            let r = self.try_lazy_head_congruence(ctx, a, b);')],
 'R42_no_rescue_restore': [(T, '        let r = f();\n        ' + L + '\n        r', '        let r = f();\n        let _ = cut;\n        r')],
 'R43_xcache_hit_no_restore': [(T, '                self.whnf_cache_insert(force_eager, k, r.clone());\n                ' + L, '                self.whnf_cache_insert(force_eager, k, r.clone());\n                let _ = cut;')],
}
if __name__ == '__main__':
    if sys.argv[1] == '--list':
        print(' '.join(M)); sys.exit(0)
    mid = sys.argv[1]; root = sys.argv[2] if len(sys.argv) > 2 else '.'
    for path, old, new in M[mid]:
        p = os.path.join(root, path)
        s = open(p).read()
        if s.count(old) != 1:
            print(f'MUTANT_ERROR {mid}: {s.count(old)} matches for {old[:60]!r}'); sys.exit(3)
        open(p, 'w').write(s.replace(old, new))
    print('applied', mid)
