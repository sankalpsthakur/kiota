set_option Elab.async false
set_option genSizeOf false
namespace R2B
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

-- B1 reflexive nested: List under a Pi
inductive RT where
  | leaf : RT
  | mk : (Nat → List RT) → RT
noncomputable def RT.sz (t : RT) : Nat :=
  @RT.rec (fun _ => Nat) (fun _ => Nat) 1 (fun _ ih => ih 0 + 10 * ih 3 + 1000) 0 (fun _ _ i j => i + j + 7) t
theorem b1_true : RT.sz (.mk (fun n => List.replicate (n+1) .leaf)) = 1328 := rfl
def b1_false : Prop := RT.sz (.mk (fun n => List.replicate (n+1) .leaf)) = 1329
-- B5 coinciding indexed auxiliaries (Wrap W vs W)
abbrev Wrap (α : Type) : Type := α
inductive W where
  | leaf : W
  | a : Vec (Wrap W) 1 → W
  | b : Vec W 1 → W
noncomputable def W.f (t : W) : Nat :=
  @W.rec (fun _ => Nat) (fun _ _ => Nat) (fun _ _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih + 10)
    0 (fun {_} _ _ i j => i + j) 100 (fun {_} _ _ i j => i + j) t
theorem b5a_true : W.f (W.a (Vec.cons W.leaf Vec.nil : Vec W 1)) = 1 := rfl
def b5a_false : Prop := W.f (W.a (Vec.cons W.leaf Vec.nil : Vec W 1)) = 101
theorem b5b_true : W.f (W.b (Vec.cons W.leaf Vec.nil : Vec (Wrap W) 1)) = 110 := rfl
def b5b_false : Prop := W.f (W.b (Vec.cons W.leaf Vec.nil : Vec (Wrap W) 1)) = 10
-- B6 reflexive through a container structure
structure Fn (α : Type) where
  f : Nat → α
inductive FT where
  | leaf : Nat → FT
  | mk : Fn FT → FT
noncomputable def FT.h (t : FT) : Nat :=
  @FT.rec (fun _ => Nat) (fun _ => Nat) (fun n => n) (fun _ ih => ih + 1) (fun _ ih => ih 0 + ih 1 * 100) t
noncomputable def FT.g (x : Fn FT) : Nat :=
  @FT.rec_1 (fun _ => Nat) (fun _ => Nat) (fun n => n) (fun _ ih => ih + 1) (fun _ ih => ih 0 + ih 1 * 100) x
theorem b6_true : FT.h (.mk ⟨fun n => .leaf (n+5)⟩) = 606 := rfl
def b6_false : Prop := FT.h (.mk ⟨fun n => .leaf (n+5)⟩) = 605
theorem b6e_true : ∀ x : Fn FT, FT.g x = FT.h (x.f 0) + FT.h (x.f 1) * 100 := fun _ => rfl
def b6e_false : Prop := ∀ x : Fn FT, FT.g x = FT.h (x.f 1) + FT.h (x.f 0) * 100
-- B7 chained: Box (indexed Vec inside, under a dependent binder)
inductive Box (α : Type) where
  | mk : (n : Nat) → Vec α n → Box α
inductive BT where
  | leaf : BT
  | mk : Box BT → BT
noncomputable def BT.s (t : BT) : Nat :=
  @BT.rec (fun _ => Nat) (fun _ => Nat) (fun _ _ => Nat) 1 (fun _ ih => ih + 1000) (fun n _ ih => ih + n * 10)
    0 (fun {_} _ _ i j => i + j) t
theorem b7_true : BT.s (.mk (.mk 2 (.cons .leaf (.cons (.mk (.mk 0 .nil)) .nil)))) = 2021 := rfl
def b7_false : Prop := BT.s (.mk (.mk 2 (.cons .leaf (.cons (.mk (.mk 0 .nil)) .nil)))) = 2011
end R2B
