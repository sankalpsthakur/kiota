/-
Sources of the `deep-ind-*` fixtures (Lean 4.36.0,
`lean -o DeepInd.olean DeepInd.lean`, then
`LEAN_PATH=.:$LEAN/lib/lean leanexport DeepInd -- DeepInd.I`): deep-ind-open-length.accept.

An inductive whose constructor field is `I u` only after the length of a
20,000-element list over the variable `u` is computed. leanchecker accepts it.
-/
namespace DeepInd
set_option maxRecDepth 200000
/-- `Nat.rec` of `n` steps that returns `P` unchanged. -/
abbrev Same (P : Prop) (n : Nat) : Prop :=
  Nat.rec (motive := fun _ => Prop) P (fun _ ih => ih) n
inductive I (u : Unit) : Prop
  | mk : Same (I u) ((List.replicate 20000 u).length + 0) → I u
end DeepInd
