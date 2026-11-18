/-
Source of `ite-distinct-open-conditions.reject.ndjson` (Lean 4.33.0,
lean4export df81913):

  lean -o Twin.olean Twin.lean
  LEAN_PATH=$PWD lean4export Twin -- R2.bad > ite-distinct-open-conditions.reject.ndjson

`R2.bad : ∀ (b c : Bool), (if b = true then true else false) = (if c = true then true else false)`
with value `fun b c => Eq.refl _`, admitted with the kernel check skipped.
With `debug.skipKernelTC` removed Lean answers "(kernel) declaration type
mismatch". The reject twin of `conleche-ite-open-hash-condition`: two `ite`s
are equal argument by argument or not at all.
-/
import Lean
open Lean Elab Command Meta

namespace R2
/-- Two `ite`s over different open conditions: not definitionally equal. -/
def lhs (b _c : Bool) : Bool := if b = true then true else false
def rhs (_b c : Bool) : Bool := if c = true then true else false
end R2

set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let b := mkConst ``Bool
  let t := mkConst ``Bool.true
  let f := mkConst ``Bool.false
  -- ∀ (b c : Bool), (if b = true then true else false) = (if c = true then true else false)
  let cond (x : Expr) := mkApp3 (mkConst ``Eq [1]) b x t
  let inst (x : Expr) := mkApp2 (mkConst ``instDecidableEqBool) x t
  let ite (x : Expr) := mkApp5 (mkConst ``ite [1]) b (cond x) (inst x) t f
  let type := mkForall `b .default b <| mkForall `c .default b <|
    mkApp3 (mkConst ``Eq [1]) b (ite (.bvar 1)) (ite (.bvar 0))
  let value := mkLambda `b .default b <| mkLambda `c .default b <|
    mkApp2 (mkConst ``Eq.refl [1]) b (ite (.bvar 1))
  addDecl <| .thmDecl { name := `R2.bad, levelParams := [], type, value }
