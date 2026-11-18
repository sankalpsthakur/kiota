set_option autoImplicit false
namespace Snd
inductive N : Type
  | z | o
inductive C (α : Type) : Type
  | a : C α
  | b : C α
inductive P (α : Type) : Type
  | p : α → P α
inductive Tr : Type
  | mk : C Tr → C (P Tr) → Tr
def id' (α : Type) : Type := α
noncomputable def X : N :=
  @Tr.rec_1 (fun _ => N) (fun _ => N) (fun _ => N)
    (fun _ _ _ _ => N.z) N.z N.o N.z N.z (@C.a (id' Tr))
theorem good : @Eq N X N.z := @Eq.refl N N.z
def badTy : Prop := @Eq N X N.o
theorem badVal : @Eq N N.o N.o := @Eq.refl N N.o
end Snd
