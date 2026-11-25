set_option Elab.async false
namespace R2D
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)
-- reflexive + indexed: the forced IH is built under a binder whose index depends on it
inductive RV where
  | leaf : RV
  | mk : ((n : Nat) → Vec RV n) → RV
noncomputable def RV.s (t : RV) : Nat :=
  @RV.rec (fun _ => Nat) (fun _ _ => Nat) 1 (fun _ ih => ih 0 + 10 * ih 2 + 1000) 0 (fun {_} _ _ i j => i + j + 7) t
def RV.vs : (n : Nat) → Vec RV n
  | 0 => .nil
  | n+1 => .cons .leaf (RV.vs n)
theorem d1_true : RV.s (.mk RV.vs) = 1160 := rfl
def d1_false : Prop := RV.s (.mk RV.vs) = 1016
end R2D
