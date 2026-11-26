-- Sources of tests/fixtures/reserved-nested-quoted-name{,-use}.accept.ndjson
-- (lean4export, Lean 4.36.0): `«_nested.Tr2»` is the single name component
-- "_nested.Tr2", not the root `_nested` that check_no_nested_aux reserves,
-- so Lean accepts the inductive and every block that mentions it.

set_option Elab.async false
def _nested.foo : Nat := 3
theorem nst_def_use : _nested.foo = 3 := rfl
structure Wrap where
  x : Nat := _nested.foo
theorem nst_wrap : (Wrap.mk 5).x = 5 := rfl
inductive «_nested.Tr2» where
  | a : «_nested.Tr2»
  | b : «_nested.Tr2» → «_nested.Tr2»
theorem nst_esc : («_nested.Tr2».b .a) ≠ .a := fun h => «_nested.Tr2».noConfusion h
inductive Esc2 where
  | mk : «_nested.Tr2» → Esc2
