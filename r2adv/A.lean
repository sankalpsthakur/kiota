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

-- N2: mutual + nested, structural recursion (brecOn over A.rec / B.rec / aux)
mutual
inductive A where
  | leaf : Nat → A
  | node : List B → A
inductive B where
  | mk : A → A → B
end
mutual
def A.sum : A → Nat
  | .leaf n => n
  | .node bs => B.sumL bs + 1
  termination_by structural a => a
def B.sumL : List B → Nat
  | [] => 0
  | b :: bs => B.sum b + B.sumL bs
  termination_by structural l => l
def B.sum : B → Nat
  | .mk a1 a2 => A.sum a1 + 2 * A.sum a2
  termination_by structural b => b
end
theorem n2_true : A.sum (.node [.mk (.leaf 3) (.leaf 4), .mk (.node []) (.leaf 1)]) = 15 := rfl
def n2_false : Prop := A.sum (.node [.mk (.leaf 3) (.leaf 4), .mk (.node []) (.leaf 1)]) = 14

-- N3: nested through three containers (List, Option, Prod)
inductive R where
  | mk : Nat → List (Option (R × Nat)) → R
mutual
def R.sum : R → Nat
  | .mk n xs => n + R.sumL xs
  termination_by structural r => r
def R.sumL : List (Option (R × Nat)) → Nat
  | [] => 0
  | x :: xs => R.sumO x + R.sumL xs
  termination_by structural l => l
def R.sumO : Option (R × Nat) → Nat
  | none => 1000
  | some p => R.sumP p
  termination_by structural o => o
def R.sumP : R × Nat → Nat
  | (r, k) => R.sum r * 10 + k
  termination_by structural p => p
end
theorem n3_true : R.sum (.mk 1 [some (.mk 2 [none], 3), none]) = 11024 := rfl
def n3_false : Prop := R.sum (.mk 1 [some (.mk 2 [none], 3), none]) = 11025

-- N4: structure eta on an auxiliary's major (Prod), major a variable
noncomputable def R.pr (p : R × Nat) : Nat :=
  @R.rec_3 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n _ ih => n + ih) 0 (fun _ _ i j => i + j) 1000 (fun _ ih => ih) (fun _ k ih => ih * 10 + k) p
noncomputable def R.rs (r : R) : Nat :=
  @R.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n _ ih => n + ih) 0 (fun _ _ i j => i + j) 1000 (fun _ ih => ih) (fun _ k ih => ih * 10 + k) r
theorem n4_true : ∀ p : R × Nat, R.pr p = R.rs p.1 * 10 + p.2 := fun _ => rfl
def n4_false : Prop := ∀ p : R × Nat, R.pr p = R.rs p.1 * 10 + p.2 + 1

-- N5: nested through Array (Array.mk : List α → Array α, two auxiliaries)
inductive AR where
  | mk : Nat → Array AR → AR
mutual
def AR.sum : AR → Nat
  | .mk n xs => n + AR.sumA xs
  termination_by structural a => a
def AR.sumA : Array AR → Nat
  | ⟨xs⟩ => AR.sumL xs
  termination_by structural a => a
def AR.sumL : List AR → Nat
  | [] => 0
  | x :: xs => AR.sum x + 2 * AR.sumL xs
  termination_by structural l => l
end
theorem n5_true : AR.sum (.mk 1 #[.mk 2 #[], .mk 3 #[.mk 4 #[]]]) = 17 := rfl
def n5_false : Prop := AR.sum (.mk 1 #[.mk 2 #[], .mk 3 #[.mk 4 #[]]]) = 18

-- N6: indexed main type with a nested occurrence at a fixed index
inductive IT : Nat → Type where
  | leaf : IT 0
  | mk : List (IT 0) → IT 1
noncomputable def IT.size {n : Nat} (t : IT n) : Nat :=
  @IT.rec (fun _ _ => Nat) (fun _ => Nat) 1 (fun _ ih => ih + 10) 0 (fun _ _ ih1 ih2 => ih1 + 2 * ih2) n t
theorem n6_true : IT.size (.mk [.leaf, .leaf, .leaf]) = 17 := rfl
def n6_false : Prop := IT.size (.mk [.leaf, .leaf, .leaf]) = 13

-- N7: universe-polymorphic nested with parameters (ctor_us differ from us)
inductive PT.{u} (α : Type u) : Type u where
  | leaf : α → PT α
  | mk : List (PT α × α) → PT α
noncomputable def PT.cnt.{u} {α : Type u} (t : PT α) : Nat :=
  @PT.rec.{1, u} α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => 1) (fun _ ih => ih + 100) 0
    (fun _ _ ih1 ih2 => ih1 + ih2) (fun _ _ ih => 3 * ih) t
theorem n7_true : PT.cnt (PT.mk [(PT.leaf (ULift.up.{2} 0), ULift.up 1), (PT.mk [], ULift.up 2)]) = 403 := rfl
def n7_false : Prop := PT.cnt (PT.mk [(PT.leaf (ULift.up.{2} 0), ULift.up 1), (PT.mk [], ULift.up 2)]) = 303

end R2A
