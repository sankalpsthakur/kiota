set_option Elab.async false
universe u v w
namespace R2C
inductive T1 (α : Type u) : Type u where
  | leaf : T1 α
  | mk : List.{max u u} (T1 α) → T1 α
inductive T2 (α : Type u) (β : Type v) : Type (max u v) where
  | mk : ULift.{max u v, 0} PUnit.{1} → (PUnit.{max u v + 1} → T2 α β) → T2 α β
  | nil : T2 α β
inductive T4 (α : Type u) : Type (max u u) where
  | mk : Option.{max u u} (T4 α × ULift.{max u u, u} α) → T4 α
theorem c_t1 : (T1.mk.{u} (α := PUnit) [T1.leaf, .leaf]) ≠ .leaf := by intro h; cases h
theorem c_t2 : (T2.nil.{u, v} (α := PUnit) (β := PUnit)) = .nil := rfl
def T4.depth.{z} {α : Type z} : T4 α → Nat
  | .mk none => 0
  | .mk (some (t, _)) => t.depth + 1
theorem c_t4 : (T4.mk.{0} (α := Nat) (some (.mk none, ⟨3⟩))).depth = 1 := rfl
end R2C
