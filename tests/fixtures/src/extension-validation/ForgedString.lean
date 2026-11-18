/-
A `String` that cannot have an inhabitant: its one field is a proof of
`False`. Lean's kernel gives every string literal the type `String` all the
same, so `("a").1 : False`.
-/
prelude
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option linter.unusedVariables false

/-- The code generator asks for this constant by name; lean4export leaves it out. -/
unsafe axiom lcErased : Type

inductive False : Prop

inductive String : Type where
  | mk (h : False) : String
