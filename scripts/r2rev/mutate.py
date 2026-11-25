#!/usr/bin/env python3
"""mutate.py ID SRC: apply one mutant to src/tc.rs of fix/deep-evaluation-v2 44edff2.
Each edit is (line, exact old text, new text); the line must hold the old text."""
import sys
L = 'CUT_SHORT.with(|c| c.set(cut));'
M = {
 'R01_open_terms_driven': [(6247, 'if expr::loose_bvar_range(e) > 0 || env_set!("KIOTA_NO_NAT_DRIVER") {', 'if env_set!("KIOTA_NO_NAT_DRIVER") {')],
 'R02_nat_values_kept_across_decls': [(1093, 'NAT_VALUES.with(|m| *m.borrow_mut() = FxHashMap::default());', '')],
 'R03_no_nat_values_lookup': [(6251, 'm.borrow().get(&key)', 'm.borrow().get(&usize::MAX)')],
 'R04_no_nat_memo_lookup': [(6257, 'm.borrow().get(&key)', 'm.borrow().get(&usize::MAX)')],
 'R05_no_early_decline_while_suspended': [(6262, 'if NAT_SUSPENDED.with(|s| s.borrow().is_some()) {', 'if false {')],
 'R06_never_suspend': [(6267, 'let deep = w >=', 'let deep = false && (w >='), (6269, 'CONV_DEPTH - NAT_MARGIN;', 'CONV_DEPTH - NAT_MARGIN);')],
 'R07_no_whnf_stride': [(6267, 'let deep = w >=', 'let deep = false && w >=')],
 'R08_no_core_stride': [(6268, '|| c >= bc.saturating_add(NAT_STRIDE)', '|| false')],
 'R09_no_margin': [(6269, '|| w.max(c) >= CONV_DEPTH - NAT_MARGIN;', '|| false;')],
 'R10_no_epoch_bump': [(6273, 'NO_MEMO_EPOCH.with(|n| n.set(n.get() + 1));', '')],
 'R11_whnf_memo_over_suspension': [(3166, 'if no_memo_epoch() != epoch {', 'if false {')],
 'R12_core_memo_over_suspension': [(3699, 'if no_memo_epoch() == epoch {', 'if true {')],
 'R13_defeq_false_memo_always': [(4542, 'if cacheable && (r || (no_memo_epoch() == epoch && !CUT_SHORT.with(Cell::get))) {', 'if cacheable {')],
 'R14_xwhnf_ignores_cut': [(3170, ' && !CUT_SHORT.with(Cell::get) {', ' {')],
 'R15_driver_keeps_ok_after_suspension': [(6316, 'NAT_SUSPENDED.with(|s| s.borrow_mut().take()) {', 'NAT_SUSPENDED.with(|s| s.borrow_mut().take()).filter(|_| r.is_err()) {')],
 'R16_no_again_check': [(6321, 'let again = pending', 'let again = false && pending')],
 'R17_no_pending_cap': [(6324, '|| pending.len() >= NAT_PENDING_CAP.with(Cell::get)', '|| false')],
 'R18_no_suspension_cap': [(6325, '|| suspensions > NAT_MAX_SUSPENSIONS', '|| false')],
 'R19_remember_while_suspended': [(6284, ' && NAT_SUSPENDED.with(|s| s.borrow().is_none())', '')],
 'R20_driver_no_cut_restore': [(6317, L, '')],
 'R21_no_conclusive_decl': [(1114, 'Self::conclusive(|| self.check_decl_once_go(name, kind))', 'self.check_decl_once_go(name, kind)')],
 'R22_no_conclusive_ind_structure': [(7114, 'Self::conclusive(|| self.check_inductive_group_structure_go(first_name))', 'self.check_inductive_group_structure_go(first_name)')],
 'R23_no_conclusive_large_elim': [(7671, 'Self::conclusive(|| self.check_inductive_group_large_elim(first_name))', 'self.check_inductive_group_large_elim(first_name)')],
 'R24_limit_hit_sets_no_cut': [(241, 'CUT_SHORT.with(|c| c.set(true));', '')],
 'R25_ensure_depth_uncounted': [(1495, 'note_limit_hit("ensure depth");', '')],
 'R26_infer_depth_uncounted': [(1571, 'note_limit_hit("infer depth");', '')],
 'R27_whnf_depth_uncounted': [(3057, 'note_limit_hit("whnf depth");', '')],
 'R28_core_depth_uncounted': [(3667, 'note_limit_hit("core depth");', '')],
 'R29_defeq_depth_uncounted': [(4301, 'note_limit_hit("defeq depth");', '')],
 'R30_huge_run_uncounted': [(5216, 'note_limit_hit("huge literal run");', '')],
 'R31_peel_budget_uncounted': [(5226, 'note_limit_hit("peel budget");', '')],
 'R32_driver_budget_uncounted': [(6327, 'note_limit_hit("nat driver budget");', '')],
 'R33_no_shape_clear': [(3115, 'if CUT_SHORT.with(Cell::get) && self.whnf_by_shape(r) {', 'if false {')],
 'R34_true_keeps_cut': [(4312, 'c.set(cut || (c.get() && !matches!(r, Ok(true))))', 'c.set(cut || c.get())')],
 'R35_defeq_drops_entry_cut': [(4312, 'c.set(cut || (c.get() && !matches!(r, Ok(true))))', 'c.set(c.get() && !matches!(r, Ok(true)))')],
 'R36_whnf_drops_entry_cut': [(3107, 'CUT_SHORT.with(|c| c.set(cut || c.get()));', '')],
 'R37_core_drops_entry_cut': [(3703, 'CUT_SHORT.with(|c| c.set(cut || c.get()));', '')],
 'R38_no_cache_marks': [(4374, 'CUT_SHORT.with(Cell::get));', 'false);'), (4396, 'CUT_SHORT.with(Cell::get));', 'false);')],
 'R39_no_cache_mark_reads': [(4365, 'if r.is_some() && cut_short_key(', 'if false && cut_short_key('), (4387, 'if r.is_some() && cut_short_key(', 'if false && cut_short_key(')],
 'R40_no_speculative_restore': [(4510, L, ''), (4520, L, '')],
 'R41_no_lazy_head_restore': [(4579, L, '')],
 'R42_no_rescue_restore': [(8892, L, '')],
 'R43_xcache_hit_no_restore': [(3096, L, '')],
}
if __name__ == '__main__':
    mid, path = sys.argv[1], sys.argv[2]
    lines = open(path).read().split('\n')
    for ln, old, new in M[mid]:
        assert old in lines[ln - 1], (mid, ln, lines[ln - 1])
        lines[ln - 1] = lines[ln - 1].replace(old, new, 1)
    open(path, 'w').write('\n'.join(lines))
    print('applied', mid)
