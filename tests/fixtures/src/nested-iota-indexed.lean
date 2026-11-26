-- Sources of tests/fixtures/nested-iota-indexed-*.ndjson: nested inductives whose
-- auxiliary member is an indexed family (Vec T n), so the forced induction
-- hypothesis must pass the container's indices. Each accept file is the
-- lean4export (Lean 4.36.0) export of one section's `*_true` theorem; its
-- -false twin appends `theorem bad_*_false : *_false := <proof of *_true>`,
-- which Lean's kernel (leanchecker 4.36) refuses. n1, n1b come from
-- namespace R2A, d1 from R2D, b5a and b7 from R2B; each was a separate file.

-- ===== R2A =====
set_option Elab.async false
namespace R2A

-- N1: nested through an indexed family (Vec T n); the forced IH passes Vec's index
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

inductive VT where
  | leaf : VT
  | mk : (n : Nat) → Vec VT n → VT

noncomputable def VT.size (t : VT) : Nat :=
  @VT.rec (fun _ => Nat) (fun _ _ => Nat) 1 (fun _ _ ih => ih + 10) 0 (fun {_} _ _ ih1 ih2 => ih1 + ih2 + 100) t
theorem n1_true : VT.size (.mk 2 (.cons .leaf (.cons .leaf .nil))) = 212 := rfl
def n1_false : Prop := VT.size (.mk 2 (.cons .leaf (.cons .leaf .nil))) = 112

-- N1b: the aux recursor applied directly at an indexed major, index written as a redex
noncomputable def VT.sizeV {n : Nat} (v : Vec VT n) : Nat :=
  @VT.rec_1 (fun _ => Nat) (fun _ _ => Nat) 1 (fun _ _ ih => ih + 10) 0 (fun {_} _ _ ih1 ih2 => ih1 + ih2 + 100) n v
theorem n1b_true : VT.sizeV (n := (fun k => k + 1) 1) (.cons (.mk 1 (.cons .leaf .nil)) (.cons .leaf .nil)) = 312 := rfl
def n1b_false : Prop := VT.sizeV (n := (fun k => k + 1) 1) (.cons (.mk 1 (.cons .leaf .nil)) (.cons .leaf .nil)) = 212
end R2A

-- ===== R2D =====
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

-- ===== R2B (B5, B7) =====
set_option genSizeOf false
namespace R2B
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

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
