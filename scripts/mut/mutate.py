#!/usr/bin/env python3
"""mutate.py ID SRC: apply mutant ID to src/tc.rs of fix/deep-evaluation-v2 8fae723 (src lines as in 48d83ba).
Each mutant names (line, exact old text, new text); the line must hold the old text."""
import sys
M = {
 'M01_driver_off': [(6242, 'if expr::loose_bvar_range(e) > 0 || env_set!("KIOTA_NO_NAT_DRIVER") {', 'if true {')],
 'M02_never_suspend': [(6262, 'let deep = w >=', 'let deep = false && (w >='), (6264, 'CONV_DEPTH - NAT_MARGIN;', 'CONV_DEPTH - NAT_MARGIN);')],
 'M02a_no_whnf_stride': [(6262, 'let deep = w >=', 'let deep = false && w >=')],
 'M02b_no_core_stride': [(6263, '|| c >= bc.saturating_add(NAT_STRIDE)', '|| false')],
 'M03_no_epoch_on_suspend': [(6268, 'NO_MEMO_EPOCH.with(|n| n.set(n.get() + 1));', '')],
 'M04_whnf_memo_over_suspension': [(3161, 'if no_memo_epoch() != epoch {', 'if false {')],
 'M05_core_memo_over_suspension': [(3694, 'if no_memo_epoch() == epoch {', 'if true {')],
 'M06_defeq_false_memo_always': [(4537, 'if cacheable && (r || (no_memo_epoch() == epoch && !CUT_SHORT.with(Cell::get))) {', 'if cacheable {')],
 'M07_no_reject_to_decline': [(1120, 'if CUT_SHORT.with(|c| c.replace(false)) =>', 'if false && CUT_SHORT.with(|c| c.replace(false)) =>')],
 'M08_no_shape_clear': [(3110, 'if CUT_SHORT.with(Cell::get) && self.whnf_by_shape(r) {', 'if false {')],
 'M09_no_speculative_restore': [(4505, 'CUT_SHORT.with(|c| c.set(cut));', ''), (4515, 'CUT_SHORT.with(|c| c.set(cut));', '')],
 'M10_no_fallback_restore': [(4574, 'CUT_SHORT.with(|c| c.set(cut));', '')],
 'M11_no_true_restore': [(4307, 'c.set(cut || (c.get() && !matches!(r, Ok(true))))', 'c.set(cut || c.get())')],
 'M12_no_cache_marks': [(4369, 'CUT_SHORT.with(Cell::get));', 'false);'), (4391, 'CUT_SHORT.with(Cell::get));', 'false);')],
 'M13_no_cache_mark_reads': [(4360, 'if r.is_some() && cut_short_key(', 'if false && cut_short_key('), (4382, 'if r.is_some() && cut_short_key(', 'if false && cut_short_key(')],
 'M14_no_driver_discard_restore': [(6312, 'CUT_SHORT.with(|c| c.set(cut));', '')],
 'M15_no_rescue_restore': [(8883, 'CUT_SHORT.with(|c| c.set(cut));', '')],
 'M16_no_again_check': [(6316, 'let again = pending', 'let again = false && pending')],
 'M17_no_pending_cap': [(6319, '|| pending.len() >= NAT_PENDING_CAP.with(Cell::get)', '|| false')],
 'M18_no_early_decline_while_suspended': [(6257, 'if NAT_SUSPENDED.with(|s| s.borrow().is_some()) {', 'if false {')],
 'M19_no_memo_lookup': [(6252, 'm.borrow().get(&key)', 'm.borrow().get(&usize::MAX)')],
 'M20_no_margin': [(6264, '|| w.max(c) >= CONV_DEPTH - NAT_MARGIN;', '|| false;')],
 'M21_core_abort_not_counted': [(3662, 'note_limit_hit("core depth");', '')],
 'M22_no_nat_values': [(6246, 'm.borrow().get(&key)', 'm.borrow().get(&usize::MAX)')],
}
mid, path = sys.argv[1], sys.argv[2]
lines = open(path).read().split('\n')
for ln, old, new in M[mid]:
    assert old in lines[ln - 1], (mid, ln, lines[ln - 1])
    lines[ln - 1] = lines[ln - 1].replace(old, new, 1)
open(path, 'w').write('\n'.join(lines))
print('applied', mid)
