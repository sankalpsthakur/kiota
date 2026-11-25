set_option Elab.async false
set_option genSizeOf false
namespace WR
abbrev Wrap (α : Type) : Type := α
inductive W where
  | leaf : W
  | a : List (Wrap W) → W
  | b : List W → W

noncomputable def f (t : W) : Nat :=
  @W.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    0 (fun _ ih => ih + 1) (fun _ ih => ih + 10)
    0 (fun _ _ i j => i + j) 100 (fun _ _ i j => i + j) t

-- the elaborator writes `[W.leaf]` at whatever type unification picks
theorem fa1 : f (W.a [W.leaf]) = 1 := rfl
theorem fa2 : f (W.a ([W.leaf] : List W)) = 1 := rfl
theorem fb1 : f (W.b [W.leaf]) = 110 := rfl
theorem fb2 : f (W.b ([W.leaf] : List (Wrap W))) = 110 := rfl

theorem x7_true : f (W.a ([W.leaf] : List W)) = 1 := rfl
def x7_false101 : Prop := f (W.a ([W.leaf] : List W)) = 101
theorem x8_true : f (W.b ([W.leaf] : List (Wrap W))) = 110 := rfl
def x8_false10 : Prop := f (W.b ([W.leaf] : List (Wrap W))) = 10
end WR
