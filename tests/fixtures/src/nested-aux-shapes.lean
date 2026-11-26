-- Source of tests/fixtures/ind-nested-aux-shapes.accept.ndjson (Lean 4.36.0):
--   lean -o NestedShapes.olean NestedShapes.lean
--   LEAN_PATH=.:$TOOLCHAIN/lib/lean leanexport NestedShapes -- NS.T1 NS.M1 NS.T3 NS.T4 NS.t1
-- leanchecker 4.36 accepts the export. Each block is nested, so every
-- constructor (and every copied container constructor) is checked with its
-- nested occurrences rewritten to auxiliary types: parameters, two containers
-- in one field, a reflexive field, a mutual container, three-deep nesting, an
-- indexed container, a mutual block, universe polymorphism and a Prop block.
set_option Elab.async false
namespace NS
structure P (a : Type) where
  x : a
inductive Box (α : Type) : Type where
  | mk : α → Box α
mutual
inductive Ev (α : Type) : Type where
  | nil : Ev α
  | cons : α → Od α → Ev α
inductive Od (α : Type) : Type where
  | cons : α → Ev α → Od α
end
inductive Ix (α : Type) : Nat → Type where
  | z : Ix α 0
  | s : α → Ix α n → Ix α (n + 1)
-- parameters, two containers, reflexive field, mutual container, deep nesting, indexed container
inductive T1 (β : Type) (n : Nat) : Type where
  | a : List (T1 β n) → Array (Option (T1 β n)) → T1 β n
  | b : (Nat → P (T1 β n)) → T1 β n
  | c : Ev (T1 β n) → β → T1 β n
  | d : List (List (Box (T1 β n))) → T1 β n
  | e : Ix (T1 β n) n → Ix (T1 β n) 3 → T1 β n
mutual
inductive M1 (α : Type) where
  | mk : List (M2 α) → α → M1 α
inductive M2 (α : Type) where
  | mk : Option (M1 α) → P (M1 α) → M2 α
end
universe u
inductive T3 (α : Type u) : Type u where
  | mk : List (T3 α) → α → Array (T3 α × α) → T3 α
inductive T4 : Prop where
  | mk : (Nat → And T4 True) → T4
theorem t1 : NS.T1.a (β := Nat) (n := 1) [] #[] ≠ NS.T1.b (fun _ => ⟨NS.T1.a [] #[]⟩) := by intro h; cases h
end NS
