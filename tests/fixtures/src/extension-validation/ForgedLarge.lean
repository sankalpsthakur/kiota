/-
`Nat.div` here is division for a dividend up to 16 and `0` beyond it; the
other operations are the genuine ones, written over `Nat.rec`.

`Nat.div` is validated for its kind, its type and its values on a grid of
numerals up to 13, where this one is right. The native rule is therefore on,
and `Nat.div 1000 10 = 100`, which is false for this definition, is still
accepted (as it is by Lean's own kernel, which never looks at the
definition). Closing this needs the equations of the fuel recursion
(lean4lean's `checkNatFuelRec`).
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

noncomputable def Nat.add (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ ih) b
noncomputable def Nat.mul (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih a) b
noncomputable def Nat.pred (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun n _ => n) a
noncomputable def Nat.sub (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.pred ih) b
noncomputable def Nat.ble (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun _ => Bool.true)
    (fun _ ih b => Nat.rec (motive := fun _ => Bool) Bool.false (fun m _ => ih m) b) a b

noncomputable def and (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.false b a

def four : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

/-- Division, by recursion on a fuel one more than the dividend. -/
noncomputable def realDiv (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Nat.zero)
    (fun _ ih x =>
      Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (ih (Nat.sub x b)))
        (and (Nat.ble b x) (Nat.ble (Nat.succ Nat.zero) b)))
    (Nat.succ a) a

/-- Division up to a dividend of 16, and `0` beyond. -/
noncomputable def Nat.div (a b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) Nat.zero (realDiv a b) (Nat.ble a (Nat.mul four four))
