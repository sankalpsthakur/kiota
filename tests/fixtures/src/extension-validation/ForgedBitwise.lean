/-
`Nat.bitwise` here ignores its function and returns its first number, and
`Nat.modCore` returns its first argument.

`Nat.land := Nat.bitwise and` has the right truth table, and is turned away
all the same: over this `Nat.bitwise` it does not compute what the native
rule does on small numerals (`land 1 0` is `1`). The `Nat.lor` below is
`Nat.bitwise and`, the wrong table. `Nat.modCore` has no native rule at all.
-/
prelude
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option linter.unusedVariables false
universe u

/-- The code generator asks for this constant by name; lean4export leaves it out. -/
unsafe axiom lcErased : Type

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

inductive Bool where
  | false
  | true

noncomputable def and (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.false b a

def Nat.bitwise (f : Bool → Bool → Bool) (a b : Nat) : Nat := a
def Nat.modCore (a b : Nat) : Nat := a

noncomputable def Nat.land : Nat → Nat → Nat := Nat.bitwise and
noncomputable def Nat.lor : Nat → Nat → Nat := Nat.bitwise and
