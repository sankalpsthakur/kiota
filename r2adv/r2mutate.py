#!/usr/bin/env python3
"""r2mutate.py <mutant-id> [root]: apply one guard-removal mutant to src/.
Each mutant is a list of (file, old, new, expected_count); a count mismatch aborts."""
import sys, os
M = {
 # ---- nested iota (4dad564) ----
 "N1_rule_miss_falls_back": [("src/tc.rs",
   "                Some(rule) if rule.num_fields as usize == num_fields => Some(Some(rule)),\n                _ => None,",
   "                Some(rule) if rule.num_fields as usize == num_fields => Some(Some(rule)),\n                _ => Some(None),", 1)],
 "N2_no_num_fields_check": [("src/tc.rs",
   "Some(rule) if rule.num_fields as usize == num_fields => Some(Some(rule)),",
   "Some(rule) => Some(Some(rule)),", 1)],
 "N3_no_ih_count_check": [("src/tc.rs",
   "        if nested_rule.is_some_and(|rule| rule.ihs.len() != rec_calls.len()) {\n            return Ok(None);\n        }",
   "", 1)],
 "N4_forced_none_skips_ih": [("src/tc.rs",
   "                            Some(rec_call) => rec_calls.push(rec_call),\n                            None => return Ok(None),",
   "                            Some(rec_call) => rec_calls.push(rec_call),\n                            None => {}", 1)],
 "N5_no_main_aux_kind_check": [("src/tc.rs",
   "if f_nparams != params.len() || frec_is_main != all.contains(&target) {",
   "if f_nparams != params.len() {", 1)],
 "N6_no_rec_of_target_check": [("src/tc.rs",
   "if self.env.rec_of.get(&target) != Some(&frec) || iargs.len() < f_nparams {",
   "if iargs.len() < f_nparams {", 1)],
 "N7_no_forced_param_defeq": [("src/tc.rs",
   "                for (p_field, p_rec) in iargs[..f_nparams].iter().zip(params.iter()) {\n                    let p_rec_shifted = shift_at(S::IOTA, p_rec, shift_by, 0);\n                    if !self.is_def_eq(&tctx, p_field, &p_rec_shifted)? {\n                        return Ok(None);\n                    }\n                }\n                (frec,",
   "                (frec,", 1)],
 "N8_aux_no_indices": [("src/tc.rs",
   "&iargs[iargs.len() - f_nindices..],", "&iargs[iargs.len()..],", 1)],
 "N9_minor_by_name_not_table": [("src/tc.rs",
   "Some(rule) => rule.minor_idx as usize,",
   "Some(_rule) => self.ctor_minor_index(cname, rname, &all),", 2)],
 "N10_ih_not_forced": [("src/tc.rs",
   "&cctx, rname, us, all, params, motives, minors, f, &dom, Some(rec),",
   "&cctx, rname, us, all, params, motives, minors, f, &dom, { let _ = rec; None },", 1)],
 "N11_no_dup_ctor_check": [("src/parser.rs",
   "if rules.insert(rule.ctor, entry).is_some() {",
   "if rules.insert(rule.ctor, entry).is_some() && false {", 1)],
 "N12_member_outside_block_skipped": [("src/parser.rs",
   "                        return Err(TcError::Other(\n                                \"nested iota rule names a member outside the block\".into(),\n                            ));",
   "                        continue;", 1)],
 "N13_rollback_keeps_nested_iota": [("src/parser.rs",
   "                    restore(&mut env.nested_iota, name, prior)",
   "                    { let _ = (name, prior); }", 1)],
 "N14_no_table_at_all": [("src/parser.rs",
   "if ordered.len() > type_names.len() {", "if false && ordered.len() > type_names.len() {", 1)],
 # ---- inductive audit 2 (5416685) ----
 "A1_no_projects_any": [("src/tc.rs",
   "if Self::projects_any(c_typ, all, &mut Default::default()) {",
   "if false && Self::projects_any(c_typ, all, &mut Default::default()) {", 1)],
 "A2_no_nested_prefix_sig": [("src/tc.rs",
   "if self.mentions_reserved_nested(typ, &mut Default::default()) {",
   "if false && self.mentions_reserved_nested(typ, &mut Default::default()) {", 1)],
 "A3_no_nested_prefix_ctor": [("src/tc.rs",
   "if self.mentions_reserved_nested(c_typ, &mut Default::default()) {",
   "if false && self.mentions_reserved_nested(c_typ, &mut Default::default()) {", 1)],
 "A4_no_keep_written": [("src/parser.rs",
   "!self.disguised_levels.is_empty() && !self.env.consts.contains_key(&name);",
   "false && !self.disguised_levels.is_empty() && !self.env.consts.contains_key(&name);", 1)],
 "A5_conclusion_levels_defeq": [("src/tc.rs",
   "us.iter().zip(expected.iter()).any(|(a, b)| a != b)",
   "us.iter().zip(expected.iter()).any(|(a, b)| !level::is_def_eq(a, b))", 1)],
 "A6_imax_not_recorded": [("src/parser.rs",
   ".insert(idx, Rc::new(level::LevelData::IMax(la, lb)));", ".len();", 1)],
 "A7_max_not_recorded": [("src/parser.rs",
   ".insert(idx, Rc::new(level::LevelData::Max(la, lb)));", ".len();", 1)],
 "A8_nested_prefix_exact_only": [("src/tc.rs",
   's == "_nested" || s.starts_with("_nested.")', 's == "_nested"', 1)],
 "A9_no_nested_prefix_proj": [("src/tc.rs",
   "self.is_reserved_nested_name(*s) || self.mentions_reserved_nested(v, seen)",
   "self.mentions_reserved_nested(v, seen)", 1)],
 "A10_no_rule_list_check": [("src/parser.rs",
   "            if r.rules.len() != d.rules.len()\n                || r\n                    .rules\n                    .iter()\n                    .zip(d.rules.iter())\n                    .any(|(rule, (ctor, nfields))| rule.ctor != *ctor || rule.nfields != *nfields)\n            {",
   "            if false && (r.rules.len() != d.rules.len()\n                || r\n                    .rules\n                    .iter()\n                    .zip(d.rules.iter())\n                    .any(|(rule, (ctor, nfields))| rule.ctor != *ctor || rule.nfields != *nfields))\n            {", 1)],
 "A11_keep_written_even_if_declared": [("src/parser.rs",
   "!self.disguised_levels.is_empty() && !self.env.consts.contains_key(&name);",
   "!self.disguised_levels.is_empty();", 1)],
 "A12_disguised_never_cleared": [("src/parser.rs",
   "            self.disguised_levels.remove(&idx);", "            self.disguised_levels.len();", 1)],
 "N15_forced_ignored_for_nonrec": [("src/tc.rs",
   "if !is_rec && forced.is_none() {", "if !is_rec {", 1)],
 "N16_no_index_count_check": [("src/tc.rs",
   "                if iargs.len() < f_nindices {\n                    return Ok(None);\n                }\n                (\n                    frec,",
   "                (\n                    frec,", 1)],
}
def main():
    mid = sys.argv[1]; root = sys.argv[2] if len(sys.argv) > 2 else "."
    if mid == "list": print(" ".join(M)); return
    if mid == "base": return
    for f, old, new, cnt in M[mid]:
        p = os.path.join(root, f); s = open(p).read()
        c = s.count(old)
        if c != cnt: sys.exit(f"{mid}: {f}: anchor count {c} != {cnt}")
        open(p, "w").write(s.replace(old, new))
    print("applied", mid)
main()
