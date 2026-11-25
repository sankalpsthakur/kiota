set_option Elab.async false
namespace NB2
inductive T2 (α β : Type) where
  | leaf : T2 α β
  | a : List (T2 α β × α) → T2 α β
  | b : List (T2 α β × β) → T2 α β

noncomputable def f (t : T2 Nat Nat) : Nat :=
  @T2.rec Nat Nat (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    1 (fun _ ih => ih + 10) (fun _ ih => ih + 100)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    1000 (fun _ _ ih1 ih2 => ih1 + ih2 + 1)
    (fun _ s ih => ih + s) (fun _ s ih => ih + 2*s + 7) t

theorem fa_true : f (.a [(.leaf, 5)]) = 16 := rfl
def fa_false1119 : Prop := f (.a [(.leaf, 5)]) = 1119
theorem fb_true : f (.b [(.leaf, 5)]) = 1119 := rfl
def fb_false16 : Prop := f (.b [(.leaf, 5)]) = 16
theorem fab_true : f (.a [(.b [(.leaf, 3)], 4)]) = 1129 := rfl
end NB2
