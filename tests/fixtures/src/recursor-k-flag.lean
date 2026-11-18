prelude
set_option autoImplicit false
universe u
inductive Eq {α : Sort u} (a : α) : α → Prop
  | refl : Eq a a
inductive B : Type
  | t | f
inductive N : Type
  | z | o
inductive T : B → Type
  | a : T B.t
  | b : T B.f
noncomputable def X : N := @T.rec (fun _ _ => N) N.z N.o B.t T.a
theorem good : @Eq N X N.z := @Eq.refl N N.z
def badTy : Prop := @Eq N X N.o
theorem badVal : @Eq N N.o N.o := @Eq.refl N N.o
