/-
`Decidable.isTrue` and `Decidable.isFalse` are axioms here, not the
constructors of `Decidable`; `ite` and `Decidable.decide` are the genuine
definitions over the real constructors `no` and `yes`, so neither reduces at
an instance built with the axioms. `Nat` lists `succ` before `zero`.
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
  | succ (n : Nat) : Nat
  | zero : Nat

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

inductive Bool where
  | false
  | true

inductive True : Prop where
  | intro

inductive False : Prop

def Not (a : Prop) : Prop := a → False

inductive Decidable (p : Prop) where
  | no (h : Not p) : Decidable p
  | yes (h : p) : Decidable p

axiom Decidable.isTrue {p : Prop} (h : p) : Decidable p
axiom Decidable.isFalse {p : Prop} (h : Not p) : Decidable p

noncomputable def ite {α : Sort u} (c : Prop) (h : Decidable c) (t e : α) : α :=
  Decidable.rec (motive := fun _ => α) (fun _ => e) (fun _ => t) h

noncomputable def dite {α : Sort u} (c : Prop) (h : Decidable c) (t : c → α) (e : Not c → α) : α :=
  Decidable.rec (motive := fun _ => α) (fun hn => e hn) (fun hp => t hp) h

noncomputable def Decidable.decide (p : Prop) (h : Decidable p) : Bool :=
  Decidable.rec (motive := fun _ => Bool) (fun _ => Bool.false) (fun _ => Bool.true) h

/-- With `succ` first, `Nat.rec` takes the successor case first. -/
noncomputable def Nat.isZero (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (fun _ _ => Bool.false) Bool.true n
