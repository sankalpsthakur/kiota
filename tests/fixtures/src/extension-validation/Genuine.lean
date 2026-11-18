/-
The extension constants with the definitions Lean gives them, written over
the recursors so that the file needs nothing but itself. Every one passes
the validation, so the theorems `forged_fixtures.py` appends are decided by
the native reductions: their literals are far too large to count down.
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

inductive True : Prop where
  | intro

inductive False : Prop

def Not (a : Prop) : Prop := a → False

inductive Decidable (p : Prop) where
  | isFalse (h : Not p) : Decidable p
  | isTrue (h : p) : Decidable p

noncomputable def Nat.add (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ ih) b
noncomputable def Nat.mul (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih a) b
noncomputable def Nat.pow (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.succ Nat.zero) (fun _ ih => Nat.mul ih a) b
noncomputable def Nat.pred (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun n _ => n) a
noncomputable def Nat.sub (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.pred ih) b
noncomputable def Nat.beq (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun b => Nat.rec (motive := fun _ => Bool) Bool.true (fun _ _ => Bool.false) b)
    (fun _ ih b => Nat.rec (motive := fun _ => Bool) Bool.false (fun m _ => ih m) b) a b
noncomputable def Nat.ble (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun _ => Bool.true)
    (fun _ ih b => Nat.rec (motive := fun _ => Bool) Bool.false (fun m _ => ih m) b) a b
noncomputable def Nat.shiftLeft (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun _ ih a => ih (Nat.mul (Nat.succ (Nat.succ Nat.zero)) a)) b a

noncomputable def ite {α : Sort u} (c : Prop) (h : Decidable c) (t e : α) : α :=
  Decidable.rec (motive := fun _ => α) (fun _ => e) (fun _ => t) h

noncomputable def dite {α : Sort u} (c : Prop) (h : Decidable c) (t : c → α) (e : Not c → α) : α :=
  Decidable.rec (motive := fun _ => α) (fun hn => e hn) (fun hp => t hp) h

noncomputable def Decidable.decide (p : Prop) (h : Decidable p) : Bool :=
  Decidable.rec (motive := fun _ => Bool) (fun _ => Bool.false) (fun _ => Bool.true) h
