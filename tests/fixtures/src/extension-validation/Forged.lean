/-
A prelude that is not Lean's: the names the kernel's extensions go by,
declared with other definitions. Exported with lean4export, then
`forged_fixtures.py` appends one theorem per fixture, since Lean itself
rejects most of them.
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

/-- Not addition: the second argument. -/
def Nat.add (a b : Nat) : Nat := b
/-- Not multiplication: the first argument. -/
def Nat.mul (a b : Nat) : Nat := a
/-- Not exponentiation. -/
def Nat.pow (a b : Nat) : Nat := a
/-- Not the predecessor: the identity. -/
def Nat.pred (a : Nat) : Nat := a
/-- Subtraction over that `pred`: `sub a b = a`. -/
noncomputable def Nat.sub (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.pred ih) b
/-- Not equality: constantly `true`. -/
def Nat.beq (a b : Nat) : Bool := Bool.true
/-- Not `≤`: constantly `false`. -/
def Nat.ble (a b : Nat) : Bool := Bool.false
/-- Not a shift: the first argument. -/
def Nat.shiftLeft (a b : Nat) : Nat := a
/-- Not a shift. -/
def Nat.shiftRight (a b : Nat) : Nat := a
def Nat.div (a b : Nat) : Nat := a
def Nat.mod (a b : Nat) : Nat := a
def Nat.gcd (a b : Nat) : Nat := a
def Nat.land (a b : Nat) : Nat := a
def Nat.lor (a b : Nat) : Nat := a
def Nat.xor (a b : Nat) : Nat := a

/-- `ite` with its branches swapped. -/
noncomputable def ite {α : Sort u} (c : Prop) (h : Decidable c) (t e : α) : α :=
  Decidable.rec (motive := fun _ => α) (fun _ => t) (fun _ => e) h

/-- `dite` with no definition at all. -/
axiom dite {α : Sort u} (c : Prop) (h : Decidable c) (t : c → α) (e : Not c → α) : α

/-- `decide` that answers `false` for a true proposition. -/
noncomputable def Decidable.decide (p : Prop) (h : Decidable p) : Bool :=
  Decidable.rec (motive := fun _ => Bool) (fun _ => Bool.true) (fun _ => Bool.false) h
