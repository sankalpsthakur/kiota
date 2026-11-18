/-
Source of `decide-distinct-open-propositions.reject.ndjson` (Lean 4.33.0,
lean4export df81913):

  lean -o TwinD.olean TwinD.lean
  LEAN_PATH=$PWD lean4export TwinD -- D2.bad > decide-distinct-open-propositions.reject.ndjson

`D2.bad : ∀ (b c : Bool), decide (b = true) = decide (c = true)` with value
`fun b c => Eq.refl _`, admitted with the kernel check skipped. With
`debug.skipKernelTC` removed Lean answers "(kernel) declaration type
mismatch". The reject twin of `conleche-decide-open-uint64-argument`: two
`decide`s are equal argument by argument or not at all.
-/
import Lean
open Lean Elab Command Meta

set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let b := mkConst ``Bool
  let t := mkConst ``Bool.true
  -- ∀ (b c : Bool), decide (b = true) = decide (c = true)
  let cond (x : Expr) := mkApp3 (mkConst ``Eq [1]) b x t
  let inst (x : Expr) := mkApp2 (mkConst ``instDecidableEqBool) x t
  let dec (x : Expr) := mkApp2 (mkConst ``Decidable.decide) (cond x) (inst x)
  let type := mkForall `b .default b <| mkForall `c .default b <|
    mkApp3 (mkConst ``Eq [1]) b (dec (.bvar 1)) (dec (.bvar 0))
  let value := mkLambda `b .default b <| mkLambda `c .default b <|
    mkApp2 (mkConst ``Eq.refl [1]) b (dec (.bvar 1))
  addDecl <| .thmDecl { name := `D2.bad, levelParams := [], type, value }
